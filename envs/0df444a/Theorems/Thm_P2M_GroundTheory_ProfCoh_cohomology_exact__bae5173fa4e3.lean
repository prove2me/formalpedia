-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3
-- name    : P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:17.231438+00:00
-- url     : https://prove2.me/theorems/cd784c31-66e8-4ba5-a14b-4e512886fcde
-- title:
--   P2 M Ground Theory Prof Coh cohomology exact  bae5173fa4e3: P2 M Ground Theory Prof Coh cohomology exact  bae5173fa4e3
-- statement:
--   The P2 M Ground Theory Prof Coh cohomology exact  bae5173fa4e3 construction uses the P2 M Ground Theory Prof Coh cohomology exact  bae5173fa4e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L82-L85

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
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
open CategoryTheory ShortComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (S : ShortComplex (Rep.{u} k G)) [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]
variable {S}
variable (hS : S.ShortExact)
include hS

theorem P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3 (i : ℕ) :
    (ShortComplex.mk (cohomologyMap S.f i) (cohomologyMap S.g i)
      (cohomologyMap_f_comp_g i)).Exact := by sorry

alias «GroundTheory».«ProfCoh».«cohomology_exact₂» := P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3
