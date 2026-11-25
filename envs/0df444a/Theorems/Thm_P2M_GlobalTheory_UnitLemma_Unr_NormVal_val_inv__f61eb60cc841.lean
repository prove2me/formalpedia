-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_inv__f61eb60cc841
-- name    : P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_inv__f61eb60cc841
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:27.862261+00:00
-- url     : https://prove2.me/theorems/f0a05abe-82c0-4cab-ab4c-7b9f48626f61
-- title:
--   P2 M Global Theory Unit Lemma Unr Norm Val val inv  f61eb60cc841: P2 M Global Theory Unit Lemma Unr Norm Val val inv  f61eb60cc841
-- statement:
--   The P2 M Global Theory Unit Lemma Unr Norm Val val inv  f61eb60cc841 construction uses the P2 M Global Theory Unit Lemma Unr Norm Val val inv  f61eb60cc841 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L32-L35

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

theorem P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_inv__f61eb60cc841 {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by sorry

alias «GlobalTheory».«UnitLemma».«Unr».«NormVal».«val_inv'» := P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_inv__f61eb60cc841
