-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_subrepCohomologyCocone___app_98e7da747dcd
-- name    : P2M_GroundTheory_ProfCoh_subrepCohomologyCocone___app_98e7da747dcd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:47.234544+00:00
-- url     : https://prove2.me/theorems/2cf6e4e2-e8dc-58a3-8b63-1e7146189628
-- title:
--   P2 M Ground Theory Prof Coh subrep Cohomology Cocone   app 98e7da747dcd: P2 M Ground Theory Prof Coh subrep Cohomology Cocone   app 98e7da747dcd
-- statement:
--   The P2 M Ground Theory Prof Coh subrep Cohomology Cocone   app 98e7da747dcd construction uses the P2 M Ground Theory Prof Coh subrep Cohomology Cocone   app 98e7da747dcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitUnion.lean#L71-L74

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
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
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))
variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]

theorem P2M_GroundTheory_ProfCoh_subrepCohomologyCocone___app_98e7da747dcd (n : ℕ) (i : ι) :
    (subrepCohomologyCocone A W hW hstable n).ι.app i =
      cohomologyMap (Rep.subtype A (W i) (hstable i)) n := by sorry

alias «GroundTheory».«ProfCoh».«subrepCohomologyCocone_ι_app» := P2M_GroundTheory_ProfCoh_subrepCohomologyCocone___app_98e7da747dcd
