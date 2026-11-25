-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:49.722913+00:00
-- url     : https://prove2.me/theorems/e48cde41-1c05-4f3e-a8eb-439bacd9745d
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq smul e9836557e9c9: P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq smul e9836557e9c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq smul e9836557e9c9 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq smul e9836557e9c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9 (c : ℂ) (w : Fin n → ℂ) :
    ∑ j, ‖(c • w) j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, ‖w j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«sum_norm_sq_smul» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9
