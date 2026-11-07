-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_field_card_le_pgl_card
-- name    : QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_pgl_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:31:23.524938+00:00
-- url     : https://prove2.me/theorems/ef409f6f-4d07-4da2-846b-21fd165d78b3
-- title:
--   Projective Linear Size: field card le pgl card
-- statement:
--   The Projective Linear Size construction uses the field card le pgl card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L55-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L55-L61

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_pgl_card [Finite K] :
    Nat.card K ≤ Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by sorry
