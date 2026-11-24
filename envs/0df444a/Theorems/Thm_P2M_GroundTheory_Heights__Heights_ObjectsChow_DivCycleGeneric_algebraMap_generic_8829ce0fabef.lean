-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:36.246171+00:00
-- url     : https://prove2.me/theorems/83371536-2071-4a05-86bd-d03701e6b322
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map generic 8829ce0fabef: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map generic 8829ce0fabef
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map generic 8829ce0fabef construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic algebra Map generic 8829ce0fabef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L84-L86

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef :
    algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) =
      toGeneric n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«algebraMap_generic» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef
