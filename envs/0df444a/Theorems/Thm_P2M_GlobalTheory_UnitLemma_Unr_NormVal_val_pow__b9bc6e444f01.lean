-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01
-- name    : P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:41.468342+00:00
-- url     : https://prove2.me/theorems/71118916-4c6d-4f6f-b111-a08815e4ee8c
-- title:
--   P2 M Global Theory Unit Lemma Unr Norm Val val pow  b9bc6e444f01: P2 M Global Theory Unit Lemma Unr Norm Val val pow  b9bc6e444f01
-- statement:
--   The P2 M Global Theory Unit Lemma Unr Norm Val val pow  b9bc6e444f01 construction uses the P2 M Global Theory Unit Lemma Unr Norm Val val pow  b9bc6e444f01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L25-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01 {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by sorry

alias «GlobalTheory».«UnitLemma».«Unr».«NormVal».«val_pow'» := P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01
