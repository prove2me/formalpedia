-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DVRQuotCount_card_quot_smul_top_of_flat__a97c8dac0493
-- name    : P2M_GlobalTheory_DVRQuotCount_card_quot_smul_top_of_flat__a97c8dac0493
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:13.670955+00:00
-- url     : https://prove2.me/theorems/f2e41c4b-b6ff-43a3-88af-06187e7ad073
-- title:
--   P2 M Global Theory DVRQuot Count card quot smul top of flat  a97c8dac0493: P2 M Global Theory DVRQuot Count card quot smul top of flat  a97c8dac0493
-- statement:
--   The P2 M Global Theory DVRQuot Count card quot smul top of flat  a97c8dac0493 construction uses the P2 M Global Theory DVRQuot Count card quot smul top of flat  a97c8dac0493 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotPowSmulBoundsDvrFgModule.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotPowSmulBoundsDvrFgModule.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open GlobalTheory GlobalTheory.DVRQuotCount
open scoped TensorProduct DirectSum

theorem P2M_GlobalTheory_DVRQuotCount_card_quot_smul_top_of_flat__a97c8dac0493 {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by sorry

alias «GlobalTheory».«DVRQuotCount».«card_quot_smul_top_of_flat'» := P2M_GlobalTheory_DVRQuotCount_card_quot_smul_top_of_flat__a97c8dac0493
