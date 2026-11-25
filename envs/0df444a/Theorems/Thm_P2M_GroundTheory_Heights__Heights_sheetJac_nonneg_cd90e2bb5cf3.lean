-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3
-- name    : P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:10.707913+00:00
-- url     : https://prove2.me/theorems/fa3f10e7-77ae-43b9-bf54-87d4cc47cf1b
-- title:
--   P2 M Ground Theory Heights  Heights sheet Jac nonneg cd90e2bb5cf3: P2 M Ground Theory Heights  Heights sheet Jac nonneg cd90e2bb5cf3
-- statement:
--   The P2 M Ground Theory Heights  Heights sheet Jac nonneg cd90e2bb5cf3 construction uses the P2 M Ground Theory Heights  Heights sheet Jac nonneg cd90e2bb5cf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetComass.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetComass.lean#L19-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3 (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : 0 ≤ sheetJac s y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sheetJac_nonneg» := P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3
