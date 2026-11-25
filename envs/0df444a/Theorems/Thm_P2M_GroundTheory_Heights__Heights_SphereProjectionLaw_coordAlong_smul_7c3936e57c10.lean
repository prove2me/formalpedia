-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:55.891125+00:00
-- url     : https://prove2.me/theorems/7ed6137b-4c42-42cd-84aa-2d30b9a41580
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along smul 7c3936e57c10: P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along smul 7c3936e57c10
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along smul 7c3936e57c10 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along smul 7c3936e57c10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10 (p w : Fin n → ℂ) (c : ℂ) :
    coordAlong p (c • w) = c * coordAlong p w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«coordAlong_smul» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10
