-- Prove2me | Theorems.Thm_QECCertificates_linearIndependent_rowList_of_isReduced
-- name    : QECCertificates.linearIndependent_rowList_of_isReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:27.901711+00:00
-- url     : https://prove2.me/theorems/1fa3163e-933b-4b95-992c-db89c65f6549
-- title:
--   QECCertificates: linear Independent row List of is Reduced
-- statement:
--   **A mutually reduced list of rows is linearly independent**: evaluating at the pivot
--   column of each row separates the coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L133-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L133-L158

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

theorem QECCertificates.linearIndependent_rowList_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by sorry
