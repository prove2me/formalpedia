-- Prove2me | Theorems.Thm_RegevRecon_linear_distance
-- name    : RegevRecon.linear_distance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:52.952112+00:00
-- url     : https://prove2.me/theorems/3de47121-c962-42ac-9851-c8f3f881712c
-- title:
--   Proof of Proposition 2 — linear distance of the matching ensemble
-- statement:
--   Fix $3\le k<D$. There is a fixed $\delta>0$ such that, under the uniform matching of the $mk=nD$ edge ends,
--
--   $$
--   \Pr\{\text{some nonempty set of at most }\delta m\text{ symbols has no check incident to exactly one of its edges}\}\to0.
--   $$
--
--   The support of a nonzero codeword of $\ker B^T$ is such a set, whatever the nonzero coefficients, so the minimum distance exceeds $\delta m$ with high probability. The decoder's erasure recovery relies on this.
--
--   Differences from the source:
--   - reading: "For sufficiently small fixed δ > 0 … = o(1)" → ∃ δ > 0, ∃ ε_n → 0, for every n with k ∣ nD the probability is ≤ ε_n, with m = nD/k; reason: the common reading of o(1) along the admissible n
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Proposition 2, p.15

import Mathlib
import Definitions.Def_RegevRecon_ConfigurationModel

namespace RegevRecon

open Filter Topology

/-- **Linear distance of the matching ensemble**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Proposition 2, p.15: for `3 ≤ k < D` there is a
fixed `δ > 0` such that, under the uniform matching of the `m k = n D` edge ends, the probability that some
nonempty set of at most `δ m` symbols has no check incident to exactly one of its edges tends to `0`. A nonzero
codeword's support is such a set, whatever the nonzero coefficients. -/
theorem linear_distance {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, k ∣ n * D →
        matchingProb (m := n * D / k) (k := k) (n := n) (D := D)
          (HasSmallNoSingleCheckSet δ) ≤ ε n := by sorry

end RegevRecon
