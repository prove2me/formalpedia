-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1
-- name    : P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:52.833865+00:00
-- url     : https://prove2.me/theorems/4f2331f3-6b08-520f-828f-fd39714523c5
-- title:
--   P2 M Reciprocity Theory PGsh L2 fourier  surjective 1bda25901bf1: P2 M Reciprocity Theory PGsh L2 fourier  surjective 1bda25901bf1
-- statement:
--   The P2 M Reciprocity Theory PGsh L2 fourier  surjective 1bda25901bf1 construction uses the P2 M Reciprocity Theory PGsh L2 fourier  surjective 1bda25901bf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L193-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L193-L205

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1 (e : H ≃ AddChar N C) (σ : H ≃ N) (f : N → C) :
    ∃ w, fourier (R := R) (fun a h => e h a) w = f := by sorry

alias «ReciprocityTheory».«PGsh».«L2».«fourier'_surjective» := P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1
