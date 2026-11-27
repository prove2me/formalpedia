-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_3fb7608abfc4
-- name    : P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_3fb7608abfc4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:45.714887+00:00
-- url     : https://prove2.me/theorems/b80e37fd-39a1-572e-91d9-73c4e50a1786
-- title:
--   P2 M Ground Theory Prof Coh d   int Rep Of Monoid End 3fb7608abfc4: P2 M Ground Theory Prof Coh d   int Rep Of Monoid End 3fb7608abfc4
-- statement:
--   The P2 M Ground Theory Prof Coh d   int Rep Of Monoid End 3fb7608abfc4 construction uses the P2 M Ground Theory Prof Coh d   int Rep Of Monoid End 3fb7608abfc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)

theorem P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_3fb7608abfc4 (f : G × G → Additive M) :
    (d₂₃ (Rep.of (intRepOfMonoidEnd.{0} φ))).hom f = (d₂₃ (Rep.of (zRepOfMonoidEnd φ))).hom f := by sorry

alias «GroundTheory».«ProfCoh».«d₂₃_intRepOfMonoidEnd» := P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_3fb7608abfc4
