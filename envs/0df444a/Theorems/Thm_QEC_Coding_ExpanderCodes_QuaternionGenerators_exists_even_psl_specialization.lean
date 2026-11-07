-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_exists_even_psl_specialization
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.exists_even_psl_specialization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:07.479187+00:00
-- url     : https://prove2.me/theorems/f6f11fc0-d770-438e-a413-cb14b8ee2e7c
-- title:
--   Quaternion Generators: exists even psl specialization
-- statement:
--   Every sufficiently large even extension admits a full-degree
--   specialization whose two actual projective generators belong to PSL₂.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L49-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionSpecialization.lean#L49-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.exists_even_psl_specialization (p n : ℕ) [Fact p.Prime]
    (hOdd : 3 ≤ p) (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ (y r : GaloisField p (2 * n)) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
      (hR : r ≠ 0)
      (hRoot : r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
      (hTwo : (2 : GaloisField p (2 * n)) ≠ 0),
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectiveBase (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y hY hOne) ∈ ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectivePrime (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y ((map_ne_zero _).mpr hEpsilon) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by sorry
