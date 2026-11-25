-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e
-- name    : P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:50.841172+00:00
-- url     : https://prove2.me/theorems/5db7f281-c17f-46b0-946d-fc5b94558ae7
-- title:
--   P2 M Ground Theory Prof Coh subsingleton cohomology X  77ff456b320e: P2 M Ground Theory Prof Coh subsingleton cohomology X  77ff456b320e
-- statement:
--   The P2 M Ground Theory Prof Coh subsingleton cohomology X  77ff456b320e construction uses the P2 M Ground Theory Prof Coh subsingleton cohomology X  77ff456b320e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L57-L66

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
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
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (cohomology S.X₁ n)) (h₃ : Subsingleton (cohomology S.X₃ n)) :
    Subsingleton (cohomology S.X₂ n) := by sorry

alias «GroundTheory».«ProfCoh».«subsingleton_cohomology_X₂» := P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e
