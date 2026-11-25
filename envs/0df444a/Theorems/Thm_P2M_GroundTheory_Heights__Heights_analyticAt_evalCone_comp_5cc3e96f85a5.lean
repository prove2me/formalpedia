-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5
-- name    : P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:16.279185+00:00
-- url     : https://prove2.me/theorems/69f3475f-3b94-4d27-b691-ba601401c6dd
-- title:
--   P2 M Ground Theory Heights  Heights analytic At eval Cone comp 5cc3e96f85a5: P2 M Ground Theory Heights  Heights analytic At eval Cone comp 5cc3e96f85a5
-- statement:
--   The P2 M Ground Theory Heights  Heights analytic At eval Cone comp 5cc3e96f85a5 construction uses the P2 M Ground Theory Heights  Heights analytic At eval Cone comp 5cc3e96f85a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/AnalyticAtEvalConeComp.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/AnalyticAtEvalConeComp.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_AnalyticAtEvalConeComp
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5 {ι : Type} [Fintype ι] {n : ι → ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : E → Cone n ℂ) (u₀ : E) (hz : ∀ k i, AnalyticAt ℂ (fun u ↦ z u k i) u₀)
    (f : MvPolynomial (Coord n) ℤ) : AnalyticAt ℂ (fun u ↦ evalCone (z u) f) u₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«analyticAt_evalCone_comp» := P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5
