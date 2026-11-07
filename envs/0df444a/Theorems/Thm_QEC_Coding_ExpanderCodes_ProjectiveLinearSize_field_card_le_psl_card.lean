-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_field_card_le_psl_card
-- name    : QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_psl_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:45:35.954331+00:00
-- url     : https://prove2.me/theorems/e18e7da7-01d4-476b-8046-72064e3351a3
-- title:
--   Projective Linear Size: field card le psl card
-- statement:
--   The Projective Linear Size construction uses the field card le psl card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L51-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L51-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_psl_card [Finite K] :
    Nat.card K ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by sorry
