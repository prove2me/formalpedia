-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_21
-- name    : WeakStrongMSR.lemma_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:31:46.930849+00:00
-- url     : https://prove2.me/theorems/4082bbbd-a355-469d-84d8-8ca34e8eef7a
-- title:
--   Lemma 3.21 — repair: at most $5ckh+12c^2kh/\gamma$ queries; whp no abort, $X_J\subseteq B(c_J,3R_J)$ and $S\cup\bigcup_JX_J=X$
-- statement:
--   Run sampling, rounding and repair with absolute constant $c$, $h$ of Eq. (20), $\gamma=\tfrac12-\delta$, guess $\lambda>0$ and an LP routine that selects optimal solutions.
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following properties, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$, metric $d$ and adversary.
--   1. On every weak-distance table and every run in which rounding does not abort, repair makes at most
--   $$5ckh+\frac{12c^2kh}{\gamma}$$
--   strong queries, also when it aborts.
--   2. With probability at least $1-n^{-a}$ over the corruption set and the randomness of sampling and repair, either rounding aborts, or repair does not abort and returns a strong set $S$ and lists $X_J$ with
--   $$X_J\subseteq B(c_J,3R_J)\ \text{for every component }J\qquad\text{and}\qquad S\cup\bigcup_JX_J=X.$$
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - reading: repair makes O(k log n) additional strong queries → at most 5ckh + 12c²kh/γ strong queries on every run where rounding does not abort; reason: Lemma 3.31 with the general-δ threshold (21): 2ckh (D) + (2c/γ)(5ckh + ckh) (small lists) + ckh (witnesses) + 2ckh (U); App. A, p.36: O(kh/γ)
--   - generalization: resource bounds for the runs of the model (weak table d̃ = weakDist d C adv) → the bound holds on every run for every table w : Fin n → Fin n → ℝ; reason: the worst-case count never depends on the honesty of w; it specializes to w = weakDist d C adv
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.21, p.20 (PDF 21); Lemma 3.31, p.25 (PDF 26); App. A, pp.35–36

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling
import Definitions.Def_WeakStrongMSR_Rounding
import Definitions.Def_WeakStrongMSR_Repair
import Definitions.Def_WeakStrongMSR_Compress
import Definitions.Def_WeakStrongMSR_Test

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.21** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.20, PDF p.21; query count: Lemma 3.31, p.25, and App. A,
p.36; threshold (21), p.34).
"With high probability, whenever rounding does not abort, repair does not abort either and returns
an updated strong set S and component lists X_J satisfying 1. X_J ⊆ B(c_J, 3R_J) for every component
J; 2. S ∪ ⋃_J X_J = X; and 3. repair makes O(k log n) additional strong queries."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1`, metric `d`, adversary, guess `λ > 0` and LP routine returning
optimal solutions, with `h = hParam c δ n` and `γ = 1/2 − δ`:
1. on every weak table and every run in which rounding does not abort, repair makes at most
   `5ckh + 12c²kh/γ` strong queries (also when it aborts);
2. with probability at least `1 − n^{−a}` over the corruption set and the randomness of sampling
   and repair, either rounding aborts, or repair does not abort, every repaired list satisfies
   `X_J ⊆ B(c_J, 3R_J)`, and the strong set together with the lists covers all points.

**Formalization Note.** `O(k log n)` is the explicit `5ckh + 12c²kh/γ` of Lemma 3.31 with the
general-δ threshold (21) (App. A, p.36: `O(kh/γ)`). Components are named by their roots. -/
theorem lemma_3_21 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ adv : Adversary n,
    ∀ lam : ℝ, 0 < lam → ∀ sel : LPSelector n, SelectsOptimal sel →
      (∀ (w : Fin n → Fin n → ℝ), ∀ o ∈ (sampleLaw c k (hParam c δ n) lam sel d w).support,
        ∀ r : RoundOut n, round c k (hParam c δ n) lam d o.S.toFinset o.cands = .ok r →
        ∀ rp ∈ (repairLaw c k (hParam c δ n) (1 / 2 - δ) d w r).support,
          (rp.queries : ℝ) ≤ 5 * c * k * hParam c δ n +
            12 * (c : ℝ) ^ 2 * k * hParam c δ n / (1 / 2 - δ)) ∧
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C => roundRepairLaw c δ k lam sel d (weakDist d C adv))
          (fun _ p => match p.2 with
            | none => True
            | some ⟨r, rp⟩ => rp.aborted = false ∧
                (∀ j ∈ r.roots, rp.lists j ⊆
                  (⟨r.ctr j, 3 * r.radiusJ j⟩ : MinSumRadiiPTAS.Main.Ball n).pts d) ∧
                rp.S ∪ r.roots.biUnion rp.lists = Finset.univ) := by sorry

end WeakStrongMSR
