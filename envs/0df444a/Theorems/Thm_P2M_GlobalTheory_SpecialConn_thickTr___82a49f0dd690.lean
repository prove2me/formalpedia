-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SpecialConn_thickTr___82a49f0dd690
-- name    : P2M_GlobalTheory_SpecialConn_thickTr___82a49f0dd690
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:38.216476+00:00
-- url     : https://prove2.me/theorems/672266c5-b97b-5f2e-94cd-99faa123eb6f
-- title:
--   P2 M Global Theory Special Conn thick Tr   82a49f0dd690: P2 M Global Theory Special Conn thick Tr   82a49f0dd690
-- statement:
--   The P2 M Global Theory Special Conn thick Tr   82a49f0dd690 construction uses the P2 M Global Theory Special Conn thick Tr   82a49f0dd690 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L38-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.SpecialConn
variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

theorem P2M_GlobalTheory_SpecialConn_thickTr___82a49f0dd690 (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n := by sorry

alias «GlobalTheory».«SpecialConn».«thickTr_ι» := P2M_GlobalTheory_SpecialConn_thickTr___82a49f0dd690
