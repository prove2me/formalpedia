-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0
-- name    : P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:12.87855+00:00
-- url     : https://prove2.me/theorems/367830e2-b16f-4d74-9ab3-70ca4038c061
-- title:
--   P2 M Ground Theory Prof Coh mem coboundaries  int Rep Of Monoid End iff 8d7a2be120d0: P2 M Ground Theory Prof Coh mem coboundaries  int Rep Of Monoid End iff 8d7a2be120d0
-- statement:
--   The P2 M Ground Theory Prof Coh mem coboundaries  int Rep Of Monoid End iff 8d7a2be120d0 construction uses the P2 M Ground Theory Prof Coh mem coboundaries  int Rep Of Monoid End iff 8d7a2be120d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L30-L33

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

theorem P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0 (f : G × G → Additive M) :
    f ∈ coboundaries₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) ↔
      f ∈ coboundaries₂ (Rep.of (zRepOfMonoidEnd φ)) := by sorry

alias «GroundTheory».«ProfCoh».«mem_coboundaries₂_intRepOfMonoidEnd_iff» := P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0
