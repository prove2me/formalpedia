-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_3
-- name    : WeakStrongMSR.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:30.833983+00:00
-- url     : https://prove2.me/theorems/89b570bb-b3da-481a-9b5d-7e700f169f76
-- title:
--   Lemma 3.3 — whp every $h$-set $W$ has fewer than $h/2$ corrupt points
-- statement:
--   Let $\delta\in(0,\tfrac12)$, $\gamma=\tfrac12-\delta$, and let $h=32\lceil c\log n/(32\gamma^2)\rceil$ be the witness count. A point $x\notin W$ is corrupt for $W$ if at least $|W|/2$ of its pairs to $W$ are corrupted.
--
--   There is an absolute constant $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following property. For every $\delta\in(0,\tfrac12)$ and $n\ge n_0$, with probability at least $1-n^{-a}$ over the corruption set,
--   $$\text{every }W\subseteq X\text{ with }|W|=h\text{ has fewer than }h/2\text{ points corrupt for }W.$$
--
--   The event depends only on the corruption set, so it holds simultaneously for all adaptively chosen witness sets. It controls every median estimate of the algorithm.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.3, p.10 (PDF 11); App. A, p.35 (PDF 36), "Corrupt points"

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.3** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.10, PDF p.11; general-δ form, App. A, p.35).
"For a sufficiently large constant c, with high probability, every set W ⊆ X of size h has fewer
than h/2 points corrupt for W."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)` and `n ≥ n₀`, with probability at least `1 − n^{−a}` over the corruption set, every
set `W` of `h = hParam c δ n` points has fewer than `h/2` points corrupt for `W`.

**Formalization Note.** `h` is the witness count of Eq. (20) (App. A); `c₀`, `a` and `n₀` do not
depend on `δ` (App. A: each bound fails with probability `n^{−Ω(c)}`). -/
theorem lemma_3_3 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n →
      1 - (n : ℝ) ^ (-a) ≤ corrProb δ (fun C : Finset (Sym2 (Fin n)) =>
        ∀ W : Finset (Fin n), W.card = hParam c δ n →
          ((corruptSet C W).card : ℝ) < (hParam c δ n : ℝ) / 2) := by sorry

end WeakStrongMSR
