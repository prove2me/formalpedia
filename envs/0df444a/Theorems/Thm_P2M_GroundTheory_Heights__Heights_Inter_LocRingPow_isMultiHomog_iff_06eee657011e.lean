-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:25.19615+00:00
-- url     : https://prove2.me/theorems/057921d7-66db-40b9-9285-d71ec2d3755d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow is Multi Homog iff 06eee657011e: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow is Multi Homog iff 06eee657011e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow is Multi Homog iff 06eee657011e construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow is Multi Homog iff 06eee657011e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L29-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e {f : MRing ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
