-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeWeight_nonneg_09efcdebf9fc
-- name    : P2M_GroundTheory_Heights__Heights_tubeWeight_nonneg_09efcdebf9fc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:15.865747+00:00
-- url     : https://prove2.me/theorems/7564898c-fffe-5f40-81f4-d6c3091b6378
-- title:
--   P2 M Ground Theory Heights  Heights tube Weight nonneg 09efcdebf9fc: P2 M Ground Theory Heights  Heights tube Weight nonneg 09efcdebf9fc
-- statement:
--   The P2 M Ground Theory Heights  Heights tube Weight nonneg 09efcdebf9fc construction uses the P2 M Ground Theory Heights  Heights tube Weight nonneg 09efcdebf9fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHess.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHess.lean#L16-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHess
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
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_tubeWeight_nonneg_09efcdebf9fc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : 0 ≤ tubeWeight Q y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tubeWeight_nonneg» := P2M_GroundTheory_Heights__Heights_tubeWeight_nonneg_09efcdebf9fc
