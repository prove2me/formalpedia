-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:21.430998+00:00
-- url     : https://prove2.me/theorems/5ae4251d-68fd-47c7-ad8e-718e98a6e3c8
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic disjoint iff is Horizontal a353c136abe0: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic disjoint iff is Horizonta
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic disjoint iff is Horizontal a353c136abe0 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic disjoint iff is Horizontal a353c136abe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L98-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0 (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
      (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«disjoint_iff_isHorizontal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0
