-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d
-- name    : P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:59.754801+00:00
-- url     : https://prove2.me/theorems/330bcf12-d4e8-48bb-9867-8684d9cc352d
-- title:
--   P2 M Ground Theory Prof Coh cohomology exact  5de6903b6f2d: P2 M Ground Theory Prof Coh cohomology exact  5de6903b6f2d
-- statement:
--   The P2 M Ground Theory Prof Coh cohomology exact  5de6903b6f2d construction uses the P2 M Ground Theory Prof Coh cohomology exact  5de6903b6f2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean#L87-L89

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

theorem P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d (i j : ℕ) (hij : i + 1 = j) :
    (ShortComplex.mk (cohomologyMap S.g i) (δ hS i j hij) (comp_δ hS i j hij)).Exact := by sorry

alias «GroundTheory».«ProfCoh».«cohomology_exact₃» := P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d
