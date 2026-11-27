-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_isCoboundary__of_isCocycle__galois_6644cfbfdd0f
-- name    : P2M_GroundTheory_ProfCoh_isCoboundary__of_isCocycle__galois_6644cfbfdd0f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:46.513265+00:00
-- url     : https://prove2.me/theorems/7b6ac029-bb92-460a-8f49-c2abf76fc304
-- title:
--   P2 M Ground Theory Prof Coh is Coboundary  of is Cocycle  galois 6644cfbfdd0f: P2 M Ground Theory Prof Coh is Coboundary  of is Cocycle  galois 6644cfbfdd0f
-- statement:
--   The P2 M Ground Theory Prof Coh is Coboundary  of is Cocycle  galois 6644cfbfdd0f construction uses the P2 M Ground Theory Prof Coh is Coboundary  of is Cocycle  galois 6644cfbfdd0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean#L85-L91

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
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
open CategoryTheory CategoryTheory.Limits
universe u
open groupCohomology
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

theorem P2M_GroundTheory_ProfCoh_isCoboundary__of_isCocycle__galois_6644cfbfdd0f (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by sorry

alias «GroundTheory».«ProfCoh».«isCoboundary₁_of_isCocycle₁_galois» := P2M_GroundTheory_ProfCoh_isCoboundary__of_isCocycle__galois_6644cfbfdd0f
