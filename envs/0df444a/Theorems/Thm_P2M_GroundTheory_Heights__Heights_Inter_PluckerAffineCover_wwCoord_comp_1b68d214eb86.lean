-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:09.278626+00:00
-- url     : https://prove2.me/theorems/9faf8af5-c9df-4e1f-a200-d06d0f474076
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover ww Coord comp 1b68d214eb86: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover ww Coord comp 1b68d214eb86
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover ww Coord comp 1b68d214eb86 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover ww Coord comp 1b68d214eb86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L328-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L328-L331

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86 : T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ∘ T.yyEmb 0 = yyc S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«wwCoord_comp» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86
