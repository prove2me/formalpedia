-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2
-- name    : P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:15.839164+00:00
-- url     : https://prove2.me/theorems/a6be9c4e-e65f-43f3-bc77-fd02f90b40d5
-- title:
--   P2 M Global Theory eval Hom det Prod Poly 9518250e38f2: P2 M Global Theory eval Hom det Prod Poly 9518250e38f2
-- statement:
--   The P2 M Global Theory eval Hom det Prod Poly 9518250e38f2 construction uses the P2 M Global Theory eval Hom det Prod Poly 9518250e38f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L261-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

theorem P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2 {R S : Type*} [CommRing R] [CommRing S] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (f : R →+* S) (ξ : EntryIndex n n → S) :
    MvPolynomial.eval₂Hom f ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det := by sorry

alias «GlobalTheory».«eval₂Hom_detProdPoly» := P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2
