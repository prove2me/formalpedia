-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355
-- name    : P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:46.634705+00:00
-- url     : https://prove2.me/theorems/c76654aa-20e8-4329-b7e4-33e5c5fd8310
-- title:
--   P2 M Global Theory Unit Lemma Unr Norm Val val mul  bc11e1e41355: P2 M Global Theory Unit Lemma Unr Norm Val val mul  bc11e1e41355
-- statement:
--   The P2 M Global Theory Unit Lemma Unr Norm Val val mul  bc11e1e41355 construction uses the P2 M Global Theory Unit Lemma Unr Norm Val val mul  bc11e1e41355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L16-L21

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

theorem P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355 {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by sorry

alias «GlobalTheory».«UnitLemma».«Unr».«NormVal».«val_mul'» := P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355
