-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_coindCokernel__coindCokernelSection_b50bf5370e48
-- name    : P2M_GroundTheory_ProfCoh_coindCokernel__coindCokernelSection_b50bf5370e48
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:52.442877+00:00
-- url     : https://prove2.me/theorems/705cd897-f9ca-5434-82fc-3df7d6a64d0c
-- title:
--   P2 M Ground Theory Prof Coh coind Cokernel  coind Cokernel Section b50bf5370e48: P2 M Ground Theory Prof Coh coind Cokernel  coind Cokernel Section b50bf5370e48
-- statement:
--   The P2 M Ground Theory Prof Coh coind Cokernel  coind Cokernel Section b50bf5370e48 construction uses the P2 M Ground Theory Prof Coh coind Cokernel  coind Cokernel Section b50bf5370e48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L184-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L184-L193

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
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
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}

theorem P2M_GroundTheory_ProfCoh_coindCokernel__coindCokernelSection_b50bf5370e48 (A : Rep.{u} k G) [IsDiscreteRep A]
    (c : LocallyConstant G A ⧸ coindEmbeddingRange A) :
    (coindCokernelπ A).hom (coindCokernelSection A c) = c := by sorry

alias «GroundTheory».«ProfCoh».«coindCokernelπ_coindCokernelSection» := P2M_GroundTheory_ProfCoh_coindCokernel__coindCokernelSection_b50bf5370e48
