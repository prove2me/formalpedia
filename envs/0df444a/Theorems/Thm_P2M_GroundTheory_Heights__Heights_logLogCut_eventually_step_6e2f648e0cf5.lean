-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5
-- name    : P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:24.933063+00:00
-- url     : https://prove2.me/theorems/8222c4a1-580f-49fd-9215-e7e12245a3f3
-- title:
--   P2 M Ground Theory Heights  Heights log Log Cut eventually step 6e2f648e0cf5: P2 M Ground Theory Heights  Heights log Log Cut eventually step 6e2f648e0cf5
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Cut eventually step 6e2f648e0cf5 construction uses the P2 M Ground Theory Heights  Heights log Log Cut eventually step 6e2f648e0cf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L73-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
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

theorem P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5 {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (h0 : 0 < ‖eval y Q‖ ^ 2) (h1 : ‖eval y Q‖ ^ 2 < 1) :
    logLogCut Q k =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogCut_eventually_step» := P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5
