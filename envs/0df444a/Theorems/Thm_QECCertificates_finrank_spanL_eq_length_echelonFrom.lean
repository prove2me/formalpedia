-- Prove2me | Theorems.Thm_QECCertificates_finrank_spanL_eq_length_echelonFrom
-- name    : QECCertificates.finrank_spanL_eq_length_echelonFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:57.422488+00:00
-- url     : https://prove2.me/theorems/7e629a06-3867-44a7-b45c-99bc2e48e8d0
-- title:
--   QECCertificates: finrank span L eq length echelon From
-- statement:
--   **The rank equals the number of rows of the append-only echelon form**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L337-L346
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L337-L346

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.finrank_spanL_eq_length_echelonFrom (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (echelonFrom L).length := by sorry
