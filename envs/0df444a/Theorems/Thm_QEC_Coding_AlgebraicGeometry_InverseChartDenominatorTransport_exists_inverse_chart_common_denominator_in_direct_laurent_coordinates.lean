-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
-- name    : QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:48.353332+00:00
-- url     : https://prove2.me/theorems/fc4a55ff-94c7-4c77-be3a-58597c12fd20
-- title:
--   Inverse Chart Denominator Transport: exists inverse chart common denominator in direct laurent coordinates
-- statement:
--   Transport the already constructed direct common-denominator result through
--   the exact inverse chart.  It stops at inverse Laurent-coordinate containment;
--   no intersection or finite-dimensional conclusion is used here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L171-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L171-L218

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) :
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ (L : Submodule (Polynomial k) F), Module.Finite (Polynomial k) L →
      ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι, ∃ p : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr
            (a • (x : F)) j) =
          directLaurentToRatFunc k (inverseLaurentCoordinate k p) := by sorry
