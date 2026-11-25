-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78
-- name    : P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:30.11646+00:00
-- url     : https://prove2.me/theorems/53f14530-3654-4006-be48-0a3e0b77a317
-- title:
--   P2 M Ground Theory Heights  Heights log Log Cut eventually zero 9e7a53dadd78: P2 M Ground Theory Heights  Heights log Log Cut eventually zero 9e7a53dadd78
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Cut eventually zero 9e7a53dadd78 construction uses the P2 M Ground Theory Heights  Heights log Log Cut eventually zero 9e7a53dadd78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L34-L51

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

theorem P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78 {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : ‖eval y Q‖ ^ 2 < cutLevel k) : logLogCut Q k =ᶠ[𝓝 y] fun _ => 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogCut_eventually_zero» := P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78
