-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:23.923014+00:00
-- url     : https://prove2.me/theorems/d00a85e9-64c0-4f4e-8030-2fcc4b0e3fba
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law of Real norm sq 0f7fc2aa98eb: P2 M Ground Theory Heights  Heights Sphere Projection Law of Real norm sq 0f7fc2aa98eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law of Real norm sq 0f7fc2aa98eb construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law of Real norm sq 0f7fc2aa98eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L15-L16

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

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«ofReal_norm_sq» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
