-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_ResVal_val_mul__6c19df7bd17f
-- name    : P2M_GlobalTheory_UnitLemma_Unr_ResVal_val_mul__6c19df7bd17f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:39.026364+00:00
-- url     : https://prove2.me/theorems/3b0e30b1-2f5f-4306-b091-6883563abfbd
-- title:
--   P2 M Global Theory Unit Lemma Unr Res Val val mul  6c19df7bd17f: P2 M Global Theory Unit Lemma Unr Res Val val mul  6c19df7bd17f
-- statement:
--   The P2 M Global Theory Unit Lemma Unr Res Val val mul  6c19df7bd17f construction uses the P2 M Global Theory Unit Lemma Unr Res Val val mul  6c19df7bd17f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L46-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResVal

theorem P2M_GlobalTheory_UnitLemma_Unr_ResVal_val_mul__6c19df7bd17f {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : val K.O (x * y) = val K.O x + val K.O y := by sorry

alias «GlobalTheory».«UnitLemma».«Unr».«ResVal».«val_mul'» := P2M_GlobalTheory_UnitLemma_Unr_ResVal_val_mul__6c19df7bd17f
