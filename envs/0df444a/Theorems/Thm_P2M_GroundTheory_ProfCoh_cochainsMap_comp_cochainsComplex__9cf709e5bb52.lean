-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52
-- name    : P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:53.5851+00:00
-- url     : https://prove2.me/theorems/e31d9a5e-6310-41c6-b412-42c101385685
-- title:
--   P2 M Ground Theory Prof Coh cochains Map comp cochains Complex  9cf709e5bb52: P2 M Ground Theory Prof Coh cochains Map comp cochains Complex  9cf709e5bb52
-- statement:
--   The P2 M Ground Theory Prof Coh cochains Map comp cochains Complex  9cf709e5bb52 construction uses the P2 M Ground Theory Prof Coh cochains Map comp cochains Complex  9cf709e5bb52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L53-L57

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
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
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52 (f : A ⟶ B) :
    cochainsMap f ≫ cochainsComplexι B =
      cochainsComplexι A ≫ groupCohomology.cochainsMap (MonoidHom.id G) f := by sorry

alias «GroundTheory».«ProfCoh».«cochainsMap_comp_cochainsComplexι» := P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52
