-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9
-- name    : P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:20.846668+00:00
-- url     : https://prove2.me/theorems/3d2a0686-6567-41b3-98cf-10812921a78e
-- title:
--   P2 M Ground Theory Heights  Heights log Log Cut eventually one 3205ba4419f9: P2 M Ground Theory Heights  Heights log Log Cut eventually one 3205ba4419f9
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Cut eventually one 3205ba4419f9 construction uses the P2 M Ground Theory Heights  Heights log Log Cut eventually one 3205ba4419f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L53-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L53-L71

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

theorem P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9 {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2) :
    logLogCut Q k =ᶠ[𝓝 y] fun _ => 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogCut_eventually_one» := P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9
