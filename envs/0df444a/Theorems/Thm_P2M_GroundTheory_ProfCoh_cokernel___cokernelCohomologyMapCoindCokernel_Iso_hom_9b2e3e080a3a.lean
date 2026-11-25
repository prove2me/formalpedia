-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cokernel___cokernelCohomologyMapCoindCokernel_Iso_hom_9b2e3e080a3a
-- name    : P2M_GroundTheory_ProfCoh_cokernel___cokernelCohomologyMapCoindCokernel_Iso_hom_9b2e3e080a3a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:37.387491+00:00
-- url     : https://prove2.me/theorems/f2b2f660-7512-49dd-b07e-b83618b90bd6
-- title:
--   P2 M Ground Theory Prof Coh cokernel   cokernel Cohomology Map Coind Cokernel Iso hom 9b2e3e080a3a: P2 M Ground Theory Prof Coh cokernel   cokernel Cohomology Map Coind Cokernel Iso hom 9b2e3e080a3a
-- statement:
--   The P2 M Ground Theory Prof Coh cokernel   cokernel Cohomology Map Coind Cokernel Iso hom 9b2e3e080a3a construction uses the P2 M Ground Theory Prof Coh cokernel   cokernel Cohomology Map Coind Cokernel Iso hom 9b2e3e080a3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/CohomologyCoindCokernelIsoHom.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/CohomologyCoindCokernelIsoHom.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

theorem P2M_GroundTheory_ProfCoh_cokernel___cokernelCohomologyMapCoindCokernel_Iso_hom_9b2e3e080a3a :
    cokernel.π (cohomologyMap (coindCokernelπ A) 0) ≫
      (cokernelCohomologyMapCoindCokernelπIso A).hom = coindδ A 0 := by sorry

alias «GroundTheory».«ProfCoh».«cokernel_π_cokernelCohomologyMapCoindCokernelπIso_hom» := P2M_GroundTheory_ProfCoh_cokernel___cokernelCohomologyMapCoindCokernel_Iso_hom_9b2e3e080a3a
