-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regRing_exists_coe_9e66cd078dd3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regRing_exists_coe_9e66cd078dd3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:53.550518+00:00
-- url     : https://prove2.me/theorems/47b3ca3a-a52e-534f-aef8-5c580a68030a
-- title:
--   P2 M Ground Theory Heights  Heights Inter reg Ring exists coe 9e66cd078dd3: P2 M Ground Theory Heights  Heights Inter reg Ring exists coe 9e66cd078dd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter reg Ring exists coe 9e66cd078dd3 construction uses the P2 M Ground Theory Heights  Heights Inter reg Ring exists coe 9e66cd078dd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L46-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldExistsInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regRing_exists_coe_9e66cd078dd3 {P : Ideal (MRing ι)} {y : funField P} (hy : y ∈ regRing P) :
    ∃ b : regRing P, (b : funField P) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regRing_exists_coe» := P2M_GroundTheory_Heights__Heights_Inter_regRing_exists_coe_9e66cd078dd3
