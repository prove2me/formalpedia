-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:50:52.367794+00:00
-- url     : https://prove2.me/theorems/0856a8b4-528d-4ed9-b006-f9841ae8ffe2
-- title:
--   Cartwright Steger: order Norm One Inner Form Reduction surjective of PSL le inner Form Image
-- statement:
--   Group-theoretic endpoint of construction-specialized strong
--   approximation.  Once the actual full inner-form reduction contains finite
--   `PSL`, the genuine norm-one reduction is surjective; the proof uses only the
--   proved normality, explicit nonidentity element, and simplicity of `PSL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5534-L5568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5534-L5568

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexInnerFormImage P r level) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) := by sorry
