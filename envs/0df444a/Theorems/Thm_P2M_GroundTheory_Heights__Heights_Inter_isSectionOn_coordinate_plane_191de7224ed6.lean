-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:38.085508+00:00
-- url     : https://prove2.me/theorems/658a0ad1-4b16-5a87-a2a8-4429958831f0
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Section On coordinate plane 191de7224ed6: P2 M Ground Theory Heights  Heights Inter is Section On coordinate plane 191de7224ed6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Section On coordinate plane 191de7224ed6 construction uses the P2 M Ground Theory Heights  Heights Inter is Section On coordinate plane 191de7224ed6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NoCommonComponentCoordinatesPlane.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NoCommonComponentCoordinatesPlane.lean#L57-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

theorem P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6 (i : Fin 3) : IsSectionOn (⊥ : Ideal (MRing (PBlk 3))) (fsLine 3) (Xc 3 i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSectionOn_coordinate_plane» := P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6
