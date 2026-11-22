-- Prove2me | Theorems.Thm_QECCertificates_map_piv_insertPivot
-- name    : QECCertificates.map_piv_insertPivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:20.638834+00:00
-- url     : https://prove2.me/theorems/18514efb-72d1-4a55-92dc-037c7190287e
-- title:
--   QECCertificates: map piv insert Pivot
-- statement:
--   Inserting one row only appends `p` to the list of pivot columns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L65-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L65-L67

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

theorem QECCertificates.map_piv_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    (insertPivot D w p).map (·.2) = (D.map (·.2)) ++ [p] := by sorry
