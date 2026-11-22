-- Prove2me | Theorems.Thm_QECCertificates_vee_apply
-- name    : QECCertificates.vee_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:03.783994+00:00
-- url     : https://prove2.me/theorems/869204a3-7b4f-42bb-9cd6-215211977384
-- title:
--   QECCertificates: vee apply
-- statement:
--   The QECCertificates construction uses the vee apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L208-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L208-L209

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}

theorem QECCertificates.vee_apply (u : Fin a → Vec p) (C : VMat a s) (i : Fin p) (j : Fin s) :
    vee u C (i, j) = ∑ k, C (k, j) * u k i := by sorry

attribute [defeq] QECCertificates.vee_apply
