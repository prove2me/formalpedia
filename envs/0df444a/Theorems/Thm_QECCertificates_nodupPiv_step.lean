-- Prove2me | Theorems.Thm_QECCertificates_nodupPiv_step
-- name    : QECCertificates.nodupPiv_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:23.871807+00:00
-- url     : https://prove2.me/theorems/eaac281c-3c8c-424c-ade8-c5d9ae3e4196
-- title:
--   QECCertificates: nodup Piv step
-- statement:
--   The QECCertificates construction uses the nodup Piv step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L78-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L78-L89

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}

theorem QECCertificates.nodupPiv_step {D : List (PivRow n)} (hred : IsReduced D) (hD : NodupPiv D) (v : Vec n) :
    NodupPiv (step D v) := by sorry
