-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology__comp_cohomologyMap_a7da692661f3
-- name    : P2M_GroundTheory_ProfCoh_cohomology__comp_cohomologyMap_a7da692661f3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:04.076195+00:00
-- url     : https://prove2.me/theorems/e45a69dc-aa95-45fa-80f1-eaf773602d76
-- title:
--   P2 M Ground Theory Prof Coh cohomology  comp cohomology Map a7da692661f3: P2 M Ground Theory Prof Coh cohomology  comp cohomology Map a7da692661f3
-- statement:
--   The P2 M Ground Theory Prof Coh cohomology  comp cohomology Map a7da692661f3 construction uses the P2 M Ground Theory Prof Coh cohomology  comp cohomology Map a7da692661f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L88-L91

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

theorem P2M_GroundTheory_ProfCoh_cohomology__comp_cohomologyMap_a7da692661f3 (f : A ⟶ B) (n : ℕ) :
    cohomologyπ A n ≫ cohomologyMap f n =
      HomologicalComplex.cyclesMap (cochainsMap f) n ≫ cohomologyπ B n := by sorry

alias «GroundTheory».«ProfCoh».«cohomologyπ_comp_cohomologyMap» := P2M_GroundTheory_ProfCoh_cohomology__comp_cohomologyMap_a7da692661f3
