-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:23.405656+00:00
-- url     : https://prove2.me/theorems/3d25c94e-56af-4685-838a-031028212caa
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel taylor two is Little O 1ad3385e6223: P2 M Ground Theory Heights  Heights Hilbert Samuel taylor two is Little O 1ad3385e6223
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel taylor two is Little O 1ad3385e6223 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel taylor two is Little O 1ad3385e6223 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L13-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComplexTaylorTwo.lean#L13-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexTaylorTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«taylor_two_isLittleO» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_taylor_two_isLittleO_1ad3385e6223
