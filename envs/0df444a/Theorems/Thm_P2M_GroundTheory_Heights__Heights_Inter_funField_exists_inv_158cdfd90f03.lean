-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_funField_exists_inv_158cdfd90f03
-- name    : P2M_GroundTheory_Heights__Heights_Inter_funField_exists_inv_158cdfd90f03
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:31.668979+00:00
-- url     : https://prove2.me/theorems/8a41f615-dd87-533f-a177-4ae32d72ed3f
-- title:
--   P2 M Ground Theory Heights  Heights Inter fun Field exists inv 158cdfd90f03: P2 M Ground Theory Heights  Heights Inter fun Field exists inv 158cdfd90f03
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fun Field exists inv 158cdfd90f03 construction uses the P2 M Ground Theory Heights  Heights Inter fun Field exists inv 158cdfd90f03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L22-L44

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

theorem P2M_GroundTheory_Heights__Heights_Inter_funField_exists_inv_158cdfd90f03 {P : Ideal (MRing ι)} [hPp : P.IsPrime] (y : funField P)
    (hy : (y : FractionRing (MRing ι ⧸ P)) ≠ 0) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«funField_exists_inv» := P2M_GroundTheory_Heights__Heights_Inter_funField_exists_inv_158cdfd90f03
