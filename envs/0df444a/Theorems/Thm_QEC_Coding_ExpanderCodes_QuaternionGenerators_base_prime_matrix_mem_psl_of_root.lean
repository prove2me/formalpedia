-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_base_prime_matrix_mem_psl_of_root
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:36.235633+00:00
-- url     : https://prove2.me/theorems/1101bc5a-b638-436b-9f8f-9e982aeb37cf
-- title:
--   Quaternion Generators: base prime matrix mem psl of root
-- statement:
--   The Quaternion Generators construction uses the base prime matrix mem psl of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L34-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L34-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_root (epsilon r y s i : K)
    (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectiveBase epsilon y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectivePrime epsilon y hEpsilon hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by sorry
