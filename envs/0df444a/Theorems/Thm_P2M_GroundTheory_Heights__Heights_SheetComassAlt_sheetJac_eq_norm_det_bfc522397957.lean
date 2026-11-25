-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957
-- name    : P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:34.341424+00:00
-- url     : https://prove2.me/theorems/b2bcbfd0-4a9b-5f96-9140-6ba5dfe963bf
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Comass Alt sheet Jac eq norm det bfc522397957: P2 M Ground Theory Heights  Heights Sheet Comass Alt sheet Jac eq norm det bfc522397957
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Comass Alt sheet Jac eq norm det bfc522397957 construction uses the P2 M Ground Theory Heights  Heights Sheet Comass Alt sheet Jac eq norm det bfc522397957 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetComass.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetComass.lean#L17-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetComass
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
open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.SheetComassAlt

theorem P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957 {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetComassAlt».«sheetJac_eq_norm_det» := P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957
