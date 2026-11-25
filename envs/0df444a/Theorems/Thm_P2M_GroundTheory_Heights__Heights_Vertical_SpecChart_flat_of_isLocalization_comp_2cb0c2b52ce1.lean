-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_flat_of_isLocalization_comp_2cb0c2b52ce1
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_flat_of_isLocalization_comp_2cb0c2b52ce1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:12.038388+00:00
-- url     : https://prove2.me/theorems/888fbfb7-8326-4f9c-85b4-aaa39166e1c9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart flat of is Localization comp 2cb0c2b52ce1: P2 M Ground Theory Heights  Heights Vertical Spec Chart flat of is Localization comp 2cb0c2b52ce1
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart flat of is Localization comp 2cb0c2b52ce1 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart flat of is Localization comp 2cb0c2b52ce1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartQuot.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartQuot.lean#L41-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_flat_of_isLocalization_comp_2cb0c2b52ce1 {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : S →+* T) (hg : (g.comp (algebraMap R S)).Flat) :
    g.Flat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«flat_of_isLocalization_comp» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_flat_of_isLocalization_comp_2cb0c2b52ce1
