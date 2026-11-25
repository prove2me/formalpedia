-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8
-- name    : P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:38.783479+00:00
-- url     : https://prove2.me/theorems/0735253f-85f7-5828-959f-dd4e81c00413
-- title:
--   P2 M Ground Theory Prof Coh d   int Rep Of Monoid End c7ea4c385cf8: P2 M Ground Theory Prof Coh d   int Rep Of Monoid End c7ea4c385cf8
-- statement:
--   The P2 M Ground Theory Prof Coh d   int Rep Of Monoid End c7ea4c385cf8 construction uses the P2 M Ground Theory Prof Coh d   int Rep Of Monoid End c7ea4c385cf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L14-L16

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

theorem P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8 (f : G → Additive M) :
    (d₁₂ (Rep.of (intRepOfMonoidEnd.{0} φ))).hom f = (d₁₂ (Rep.of (zRepOfMonoidEnd φ))).hom f := by sorry

alias «GroundTheory».«ProfCoh».«d₁₂_intRepOfMonoidEnd» := P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8
