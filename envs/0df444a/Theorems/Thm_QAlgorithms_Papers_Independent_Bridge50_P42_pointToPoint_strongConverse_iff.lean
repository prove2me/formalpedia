-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P42_pointToPoint_strongConverse_iff
-- name    : QAlgorithms.Papers.Independent.Bridge50.P42.pointToPoint_strongConverse_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:04:36.875917+00:00
-- url     : https://prove2.me/theorems/7dda51aa-a1c4-4ad8-b8ba-7aa6b9b6991b
-- title:
--   Nonstationary point-to-point strong converse criterion
-- statement:
--   Let $V_j:\mathcal X\to\mathcal Y$ be normalized discrete channels on fixed finite nonempty alphabets, and let $V^n=\prod_{j=1}^nV_j$. Let $C(V_j)$ be Shannon capacity in bits, and let $\overline P_{Y,j}$ be the capacity-achieving output law obtained from a maximizing input of $V_j$. Suppose
--
--   $$\exists B<\infty\quad\forall j,x:\quad\operatorname{Var}_{Y\sim V_j(\cdot\mid x)}\!\left[\log_2\frac{V_j(Y\mid x)}{\overline P_{Y,j}(Y)}\right]\le B.$$
--
--   Zero-mass outputs do not contribute to this variance. The point-to-point channel sequence satisfies the strong converse if and only if
--
--   $$\liminf_{n\to\infty}\frac1n\sum_{j=1}^nC(V_j)=\limsup_{n\to\infty}\frac1n\sum_{j=1}^nC(V_j).$$
--
--   The strong converse is expressed as equality of ordinary zero-error-tolerance capacity and optimistic unit-error-tolerance capacity, using arbitrary stochastic encoders and deterministic decoders with average error. This is an equivalence under the variance condition.
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, PDF p. 6, §III-C2, (46)–(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF p.6, (46)–(47): the point-to-point strong converse iff the liminf
and limsup of marginal Shannon-capacity averages agree. The variance bound
is uniform over both component index and input, and uses the constructed output law. -/
theorem pointToPoint_strongConverse_iff
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (V : ℕ → X → Y → ℝ) (hV : ∀ j, StochasticRows (V j))
    (hvar : ∃ B : ℝ, ∀ j x, rowInformationVariance (V j) x ≤ B) :
    PointStrongConverse V ↔
      Filter.liminf (capacityAverage V) atTop = Filter.limsup (capacityAverage V) atTop := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P42

end
