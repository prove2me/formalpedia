-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_map_augmentationIdeal_comap_pullbackQuotient
-- name    : ReciprocityTheory.PGsh.L2.mem_map_augmentationIdeal_comap_pullbackQuotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:40.462278+00:00
-- url     : https://prove2.me/theorems/4f586972-6ffd-51f2-800d-f34aa82d58d7
-- title:
--   L2: mem map augmentation Ideal comap pullback Quotient
-- statement:
--   The L2 construction uses the mem map augmentation Ideal comap pullback Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemMapAugmentationIdealComapPullbackQuotient.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemMapAugmentationIdealComapPullbackQuotient.lean#L36-L47

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem ReciprocityTheory.PGsh.L2.mem_map_augmentationIdeal_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) (h0 : h 0 = 0) :
    h ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) := by sorry
