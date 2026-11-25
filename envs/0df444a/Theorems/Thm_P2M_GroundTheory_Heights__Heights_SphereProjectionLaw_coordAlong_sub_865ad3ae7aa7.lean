-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_sub_865ad3ae7aa7
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_sub_865ad3ae7aa7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:54.627304+00:00
-- url     : https://prove2.me/theorems/9b115166-68e0-5ad7-9759-ccaa1cdfce6d
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along sub 865ad3ae7aa7: P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along sub 865ad3ae7aa7
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along sub 865ad3ae7aa7 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law coord Along sub 865ad3ae7aa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_sub_865ad3ae7aa7 (p z w : Fin n → ℂ) :
    coordAlong p (z - w) = coordAlong p z - coordAlong p w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«coordAlong_sub» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_sub_865ad3ae7aa7
