-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_14
-- name    : WeakStrongMSR.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:00.441951+00:00
-- url     : https://prove2.me/theorems/720d9c7a-d853-4850-867d-342761164b1f
-- title:
--   Lemma 3.14 — rounding: whp no abort, $\le ckh$ queries, $<102k$ lists with $\sum_JR_J<714k\lambda$ and $X_J\setminus E\subseteq B_J$, $|E|\le 2ckh$
-- statement:
--   Run sampling and then rounding with absolute constant $c$, $h$ of Eq. (20), guess $\lambda\ge\mathrm{OPT}/(2k)$, $\lambda>0$, and an LP routine that selects optimal solutions.
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following property, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$, metric $d$ and adversary. With probability at least $1-n^{-a}$ over the corruption set and the sampling randomness, rounding does not abort and:
--   1. it makes at most $ckh$ strong queries;
--   2. its component lists are pairwise disjoint and their union is exactly the set of points it leaves unqueried;
--   3. there are fewer than $102k$ components;
--   4. every root $c_J$ is strongly queried;
--   5. $\sum_JR_J<714k\lambda$;
--   6. $X_J\setminus E\subseteq B(c_J,R_J)$ for every component, where $E$ is the set of points corrupt for the witness set of some sampled centre;
--   7. $|E|\le 2ckh$.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - reading: O(k log n) additional queries, at most O(k) nonempty lists, ∑_J R_J = O(kλ), |E| = O(kh) → ≤ ckh queries (line 6 guard), < 102k components (Lemma 3.17), ∑_J R_J < 714kλ (14·51, Lemmas 3.17, 3.19), |E| ≤ 2ckh (Lemma 3.4); reason: the explicit constants of the proof (p.19)
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.14, p.14 (PDF 15); proof p.19 (PDF 20); Lemmas 3.4, 3.16–3.20

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling
import Definitions.Def_WeakStrongMSR_Rounding

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.14** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.14, PDF p.15; constants from Lemmas 3.4, 3.16–3.20 and the
guard of Algorithm 2, line 6).
"If λ ≥ OPT/(2k), then, with high probability, the rounding step does not abort, makes O(k log n)
additional strong queries, and partitions the points it leaves unqueried into at most O(k) nonempty
lists X_J. On this event, each list has an associated ball B_J = B(c_J, R_J), where c_J is strongly
queried, such that 1. ∑_J R_J = O(kλ); and 2. X_J \ E ⊆ B_J, where the set E has size
O(kh) = O(k log n)."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1`, metric `d`, adversary, LP routine returning optimal solutions,
and guess `λ ≥ OPT/(2k)`, `λ > 0`, with `h = hParam c δ n`: with probability at least `1 − n^{−a}`
over the corruption set and the sampling randomness, rounding the sampling output does not abort,
makes at most `ckh` strong queries, its component lists are pairwise disjoint with union the set of
unqueried points, there are fewer than `102k` components, every root `c_J` is strongly queried,
`∑_J R_J < 714kλ`, every list satisfies `X_J ∖ E ⊆ B(c_J, R_J)`, and `|E| ≤ 2ckh`, where `E` is the
set of points corrupt for the witness set of some sampled centre (Definition 3.2).

**Formalization Note.** The `O(·)` bounds are the explicit constants of the proof:
`ckh` (line 6 guard), `102k` (Lemma 3.17, components ≤ selected candidates by Lemma 3.19),
`714 = 14 · 51` (Lemmas 3.17, 3.19), `2ckh` (Lemma 3.4). Components are named by their roots. -/
theorem lemma_3_14 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ adv : Adversary n,
    ∀ lam : ℝ, 0 < lam → ∀ sel : LPSelector n, SelectsOptimal sel →
    MinSumRadiiPTAS.Main.msrOpt d k / (2 * k) ≤ lam →
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C => sampleLaw c k (hParam c δ n) lam sel d (weakDist d C adv))
          (fun C o => ∃ r : RoundOut n,
            round c k (hParam c δ n) lam d o.S.toFinset o.cands = .ok r ∧
            r.queries ≤ c * k * hParam c δ n ∧
            (∀ j ∈ r.roots, ∀ j' ∈ r.roots, j ≠ j' → Disjoint (r.list j) (r.list j')) ∧
            r.roots.biUnion r.list = Finset.univ.filter (fun x => x ∉ r.S) ∧
            r.roots.card < 102 * k ∧
            (∀ j ∈ r.roots, r.ctr j ∈ r.S) ∧
            ∑ j ∈ r.roots, r.radiusJ j < 714 * k * lam ∧
            (∀ j ∈ r.roots, r.list j \ sampleE C o ⊆
              (⟨r.ctr j, r.radiusJ j⟩ : MinSumRadiiPTAS.Main.Ball n).pts d) ∧
            (sampleE C o).card ≤ 2 * c * k * hParam c δ n) := by sorry

end WeakStrongMSR
