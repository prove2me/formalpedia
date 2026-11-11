-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_1
-- name    : WeakStrongMSR.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:48.758854+00:00
-- url     : https://prove2.me/theorems/5bd8b282-2f58-4086-bb13-2e498c1646b5
-- title:
--   Lemma 3.1 — sampling: at most $2ckh$ queries; whp every candidate is a true ball up to $E_s$, and $\mathrm{OPT}_{LP}<17(\mathrm{OPT}+k\lambda)$
-- statement:
--   Run the sampling step with absolute constant $c$, witness count $h$ of Eq. (20), guess $\lambda>0$ and an LP routine that selects optimal solutions of (1).
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following properties, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$, metric $d$ and adversary.
--
--   1. On every weak-distance table and every outcome, sampling makes at most $2ckh$ strong queries.
--   2. With probability at least $1-n^{-a}$ over the corruption set and the sampling randomness, two things hold. First, every candidate $(A,s,R)$ of the final family satisfies $|E_s|<h/2$ and $A\setminus E_s\subseteq B(s,R)$, where $E_s$ is the set of points corrupt for the witness set of $s$. Second, the final LP optimum satisfies
--   $$\mathrm{OPT}_{LP}<17(\mathrm{OPT}+k\lambda).$$
--
--   The constant $17=2\alpha+1$ with $\alpha=8$ comes from the heaviness threshold of Definition 3.6.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - reading: O(k log n) strong queries; "some set E_s with |E_s| < h/2" → at most 2ckh strong queries on every run; E_s = the points corrupt for W_s; reason: the proof gives the explicit total 2ckh (p.14); Definition 3.2 names E_s
--   - generalization: resource bounds for the runs of the model (weak table d̃ = weakDist d C adv) → the bound holds on every run for every table w : Fin n → Fin n → ℝ; reason: the worst-case count never depends on the honesty of w; it specializes to w = weakDist d C adv
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.1, p.8 (PDF 9); proof pp.13–14 (PDF 14–15); App. A, pp.34–35

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.1** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.8, PDF p.9; queries: proof, p.14; general δ: App. A,
pp.34–35).
"The sampling step makes O(k log n) strong queries and returns a candidate family C such that, with
high probability, 1. for each (A(s, R), s, R) ∈ C, some set E_s with |E_s| < h/2 satisfies
A(s, R) \ E_s ⊆ B(s, R); and 2. OPT_LP < 17(OPT + kλ)."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1`, metric `d`, adversary, guess `λ > 0` and LP routine returning
optimal solutions of (1), with `h = hParam c δ n`:
1. on every weak table and every outcome, sampling makes at most `2ckh` strong queries;
2. with probability at least `1 − n^{−a}` over the corruption set and the sampling randomness,
   every candidate `(A, s, R)` of the final family satisfies `|E_s| < h/2` and `A ∖ E_s ⊆ B(s, R)`,
   where `E_s` is the set of points corrupt for the witness set `W_s` of `s`, and the final LP
   optimum satisfies `OPT_LP < 17(OPT + kλ)`.

**Formalization Note.** `O(k log n)` is the explicit `2ckh` of the proof (p.14). The set `E_s` of
clause 1 is the one of Definition 3.2 (a specific witness of the paper's "some set"). The sampling
step is `WeakStrongMSR.Sampling` with the App. A parameters. -/
theorem lemma_3_1 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ adv : Adversary n,
    ∀ lam : ℝ, 0 < lam → ∀ sel : LPSelector n, SelectsOptimal sel →
      (∀ (w : Fin n → Fin n → ℝ), ∀ o ∈ (sampleLaw c k (hParam c δ n) lam sel d w).support,
        o.S.length ≤ 2 * c * k * hParam c δ n) ∧
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C => sampleLaw c k (hParam c δ n) lam sel d (weakDist d C adv))
          (fun C o =>
            (∀ cd ∈ o.cands, ((corruptSet C cd.W).card : ℝ) < (hParam c δ n : ℝ) / 2 ∧
              cd.A \ corruptSet C cd.W ⊆ (⟨cd.s, cd.R⟩ : MinSumRadiiPTAS.Main.Ball n).pts d) ∧
            lpOpt o.S.toFinset o.cands lam (hParam c δ n) <
              17 * (MinSumRadiiPTAS.Main.msrOpt d k + k * lam)) := by sorry

end WeakStrongMSR
