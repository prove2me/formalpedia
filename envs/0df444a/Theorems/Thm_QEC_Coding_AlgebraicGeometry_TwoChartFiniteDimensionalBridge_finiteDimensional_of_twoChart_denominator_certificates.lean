-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_finiteDimensional_of_twoChart_denominator_certificates
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:36.776278+00:00
-- url     : https://prove2.me/theorems/8f0f3461-fad1-4439-80c3-0c8a949e414d
-- title:
--   Two Chart Finite Dimensional Bridge: finite Dimensional of two Chart denominator certificates
-- statement:
--   The bounded two-chart finite-dimensional bridge.  `L` is an actual
--   `k`-submodule (the later all-place valuation-bounded submodule is supplied
--   here only after its chart membership theorem is built).  The two inclusion
--   certificates target actual finite polynomial submodules, respectively under
--   the direct and the fully transported inverse action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L362-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L362-L456

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F)
    (L : Submodule k F) (Λdirect : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) Λdirect]
    (hdirectContains : ∀ x : L, (x : F) ∈ Λdirect)
    (hinverseContains :
      let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∃ Λinverse : Submodule (Polynomial k) F,
        Module.Finite (Polynomial k) Λinverse ∧
        ∀ x : L, (x : F) ∈ Λinverse) :
    FiniteDimensional k L := by sorry
