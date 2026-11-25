-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_GL_9d991f300e31
-- name    : P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_GL_9d991f300e31
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:56:17.12766+00:00
-- url     : https://prove2.me/theorems/f967c640-134e-4e28-94bc-6e50d14c018c
-- title:
--   P2 M Ground Theory Variant  N1 Map Theta TInvariant second Countable Topology GL 9d991f300e31: P2 M Ground Theory Variant  N1 Map Theta TInvariant second Countable Topology GL 9d991f300e31
-- statement:
--   The P2 M Ground Theory Variant  N1 Map Theta TInvariant second Countable Topology GL 9d991f300e31 construction uses the P2 M Ground Theory Variant  N1 Map Theta TInvariant second Countable Topology GL 9d991f300e31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean#L52-L58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
open GroundTheory.Variant₂.N1.MapThetaTInvariant
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_GL_9d991f300e31 : SecondCountableTopology (GL (Fin n) F) := by sorry

alias «GroundTheory».«Variant₂».«N1».«MapThetaTInvariant».«secondCountableTopology_GL» := P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_GL_9d991f300e31
