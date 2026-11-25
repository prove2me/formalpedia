-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_OrthBasis_herm_smul_right__c57101fb1dc8
-- name    : P2M_GlobalTheory_UnitLemma_OrthBasis_herm_smul_right__c57101fb1dc8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:18.974443+00:00
-- url     : https://prove2.me/theorems/3d32aa89-23f0-46e2-80d8-021b30b29ed3
-- title:
--   P2 M Global Theory Unit Lemma Orth Basis herm smul right  c57101fb1dc8: P2 M Global Theory Unit Lemma Orth Basis herm smul right  c57101fb1dc8
-- statement:
--   The P2 M Global Theory Unit Lemma Orth Basis herm smul right  c57101fb1dc8 construction uses the P2 M Global Theory Unit Lemma Orth Basis herm smul right  c57101fb1dc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthBasis
open GlobalTheory.UnitLemma
variable {K : UQ} (B : InvAlg K)

theorem P2M_GlobalTheory_UnitLemma_OrthBasis_herm_smul_right__c57101fb1dc8 (x y z : B.A) (a : K.E) : B.herm x y (a • z) = K.c a * B.herm x y z := by sorry

alias «GlobalTheory».«UnitLemma».«OrthBasis».«herm_smul_right'» := P2M_GlobalTheory_UnitLemma_OrthBasis_herm_smul_right__c57101fb1dc8
