-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_matrix_mul_adjugate_eq_zero_of_ker_eq
-- name    : QEC.Coding.TannerLiftedProduct.matrix_mul_adjugate_eq_zero_of_ker_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:47:05.063995+00:00
-- url     : https://prove2.me/theorems/a3554217-867f-4c0e-b3c1-442528155738
-- title:
--   Tanner Lifted Product: matrix mul adjugate eq zero of ker eq
-- statement:
--   Two singular two-by-two matrices with the same kernel annihilate after
--   multiplying the first by the adjugate of the second.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L139-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L139-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.matrix_mul_adjugate_eq_zero_of_ker_eq
    {K : Type*} [Field K] (B C : Matrix (Fin 2) (Fin 2) K)
    (hdetC : C.det = 0)
    (hker : LinearMap.ker (Matrix.toLin' B) =
      LinearMap.ker (Matrix.toLin' C)) :
    B * C.adjugate = 0 := by sorry
