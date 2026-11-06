-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_exists_common_denominator_direct_chart
-- name    : QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:56:37.17179+00:00
-- url     : https://prove2.me/theorems/6bcb8a83-c618-484f-a992-213d22eb0625
-- title:
--   Direct Chart Common Denominator: exists common denominator direct chart
-- statement:
--   A finite polynomial submodule has one actual nonzero denominator which
--   puts every coordinate of every scaled element into the direct polynomial
--   subring of `k(X)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/DirectChartCommonDenominator.lean#L57-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/DirectChartCommonDenominator.lean#L57-L118

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
open scoped BigOperators Polynomial
variable {k F ι : Type*}
variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (L : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) L] :
    ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι,
      b.repr (a • (x : F)) j ∈ Set.range (algebraMap (Polynomial k) (RatFunc k)) := by sorry
