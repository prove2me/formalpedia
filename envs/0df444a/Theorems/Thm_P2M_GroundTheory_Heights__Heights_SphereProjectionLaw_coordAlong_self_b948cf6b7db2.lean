-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:32.781553+00:00
-- url     : https://prove2.me/theorems/4410355b-80c0-425a-828e-31721023107d
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along self b948cf6b7db2: P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along self b948cf6b7db2
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along self b948cf6b7db2 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along self b948cf6b7db2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L31-L32

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

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2 {p : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) : coordAlong p p = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«coordAlong_self» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2
