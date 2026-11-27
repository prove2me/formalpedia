-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_isDiscreteRep_X__of_shortExact_bd22bfdec208
-- name    : P2M_GroundTheory_ProfCoh_isDiscreteRep_X__of_shortExact_bd22bfdec208
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:35.772096+00:00
-- url     : https://prove2.me/theorems/a62d8f3c-3780-56dd-9cc6-59e896d4fc22
-- title:
--   P2 M Ground Theory Prof Coh is Discrete Rep X  of short Exact bd22bfdec208: P2 M Ground Theory Prof Coh is Discrete Rep X  of short Exact bd22bfdec208
-- statement:
--   The P2 M Ground Theory Prof Coh is Discrete Rep X  of short Exact bd22bfdec208 construction uses the P2 M Ground Theory Prof Coh is Discrete Rep X  of short Exact bd22bfdec208 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L255-L257

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
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
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem P2M_GroundTheory_ProfCoh_isDiscreteRep_X__of_shortExact_bd22bfdec208 {S : ShortComplex (Rep.{w} k G)} (hS : S.ShortExact)
    [IsDiscreteRep S.X₂] : IsDiscreteRep S.X₃ := by sorry

alias «GroundTheory».«ProfCoh».«isDiscreteRep_X₃_of_shortExact» := P2M_GroundTheory_ProfCoh_isDiscreteRep_X__of_shortExact_bd22bfdec208
