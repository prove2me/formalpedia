-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:00.929321+00:00
-- url     : https://prove2.me/theorems/754804de-3f59-4c0c-9259-500f783e933a
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic map comap horizontal 605d4997ca31: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic map comap horizontal 605d4997ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic map comap horizontal 605d4997ca31 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic map comap horizontal 605d4997ca31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L115-L119

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31 (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
    (hW : W.IsPrime) (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W) :
    (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).comap (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«map_comap_horizontal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31
