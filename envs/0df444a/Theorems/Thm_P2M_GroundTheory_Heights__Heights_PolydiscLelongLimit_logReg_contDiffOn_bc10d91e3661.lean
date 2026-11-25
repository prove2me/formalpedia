-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_logReg_contDiffOn_bc10d91e3661
-- name    : P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_logReg_contDiffOn_bc10d91e3661
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:06.112838+00:00
-- url     : https://prove2.me/theorems/664f05cd-2158-4eb3-a15b-9001d9795bd2
-- title:
--   P2 M Ground Theory Heights  Heights Polydisc Lelong Limit log Reg cont Diff On bc10d91e3661: P2 M Ground Theory Heights  Heights Polydisc Lelong Limit log Reg cont Diff On bc10d91e3661
-- statement:
--   The P2 M Ground Theory Heights  Heights Polydisc Lelong Limit log Reg cont Diff On bc10d91e3661 construction uses the P2 M Ground Theory Heights  Heights Polydisc Lelong Limit log Reg cont Diff On bc10d91e3661 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L48-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit
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
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit

theorem P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_logReg_contDiffOn_bc10d91e3661 {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PolydiscLelongLimit».«logReg_contDiffOn» := P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_logReg_contDiffOn_bc10d91e3661
