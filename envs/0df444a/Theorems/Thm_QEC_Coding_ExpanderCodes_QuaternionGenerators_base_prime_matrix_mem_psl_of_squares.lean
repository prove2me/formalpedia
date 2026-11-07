-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_base_prime_matrix_mem_psl_of_squares
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_squares
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:43.410677+00:00
-- url     : https://prove2.me/theorems/02c4fbf1-1d9e-4349-943f-098bc302abee
-- title:
--   Quaternion Generators: base prime matrix mem psl of squares
-- statement:
--   The two independently computed norms are squares for these actual roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L19-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L19-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_squares (r y s i : K)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquiv r y hR hOne hTwo
          (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by sorry
