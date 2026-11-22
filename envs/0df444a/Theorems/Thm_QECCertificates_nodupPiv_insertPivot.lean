-- Prove2me | Theorems.Thm_QECCertificates_nodupPiv_insertPivot
-- name    : QECCertificates.nodupPiv_insertPivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:23.303244+00:00
-- url     : https://prove2.me/theorems/3ec6a6ef-849a-4eac-a889-018596de015b
-- title:
--   QECCertificates: nodup Piv insert Pivot
-- statement:
--   The QECCertificates construction uses the nodup Piv insert Pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L69-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L69-L76

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

theorem QECCertificates.nodupPiv_insertPivot {D : List (PivRow n)} (hD : NodupPiv D) {w : Vec n} {p : Fin n}
    (hp : p ∉ D.map (·.2)) : NodupPiv (insertPivot D w p) := by sorry
