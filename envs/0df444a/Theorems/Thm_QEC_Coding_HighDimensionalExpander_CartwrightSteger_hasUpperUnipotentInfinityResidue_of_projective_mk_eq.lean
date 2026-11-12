-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_hasUpperUnipotentInfinityResidue_of_projective_mk_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.hasUpperUnipotentInfinityResidue_of_projective_mk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:48.011818+00:00
-- url     : https://prove2.me/theorems/e7dd257a-3246-47bc-87cd-fecf3a1091e1
-- title:
--   Cartwright Steger: has Upper Unipotent Infinity Residue of projective mk eq
-- statement:
--   Inner conjugation, and hence the upper-unipotent infinity-residue
--   condition, is unchanged when a global matrix is multiplied by a scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L17-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L17-L74

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.hasUpperUnipotentInfinityResidue_of_projective_mk_eq
    (P : BasePrime) (r : Rank)
    {A B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hA : HasUpperUnipotentInfinityResidue P r A)
    (hprojective : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk B) :
    HasUpperUnipotentInfinityResidue P r B := by sorry
