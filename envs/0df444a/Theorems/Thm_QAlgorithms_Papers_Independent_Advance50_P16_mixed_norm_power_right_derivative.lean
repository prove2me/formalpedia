-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_mixed_norm_power_right_derivative
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.mixed_norm_power_right_derivative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:41:23.746988+00:00
-- url     : https://prove2.me/theorems/3b5eaee6-1cff-431a-9025-4f3c5f20f4ec
-- title:
--   Theorem 17: right derivative of the mixed norm power
-- statement:
--   Let $X$ be any density matrix on a nonzero finite bipartite register, and put $X_1=\operatorname{Tr}_2X$. Singular densities are allowed. In the natural-log convention,
--
--   $$\left.\frac{d}{dp}\|X\|_{(1,p)}^p\right|_{p=1+}=-S(X)+S(X_1).$$
--
--   The derivative is a right derivative of the norm's $p$th power, using the vector-valued norm from (3.2)–(3.3). This differentiation identity turns mixed-norm inequalities into entropy inequalities.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 28, Theorem 17: right derivative of the mixed norm power

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Theorem 17 / (6.3), PDF pp.28–31: the right derivative of the pth POWER of
the norm, in nats. Singular densities are included. -/
theorem mixed_norm_power_right_derivative {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (X : Mat (D × I)) (hX : IsDensityMatrix X) :
    HasDerivWithinAt (fun p : ℝ => (mixedNorm 1 (ENNReal.ofReal p) X) ^ p)
      (-entropy X + entropy (traceRight X)) (Ici 1) 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
