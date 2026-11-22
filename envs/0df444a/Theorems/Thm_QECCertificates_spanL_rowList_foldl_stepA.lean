-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_foldl_stepA
-- name    : QECCertificates.spanL_rowList_foldl_stepA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:37.713242+00:00
-- url     : https://prove2.me/theorems/033099c7-cd7d-464a-9055-2a948021f466
-- title:
--   QECCertificates: span L row List foldl step A
-- statement:
--   A generalized form of the main loop: starting from `D` and consuming `L`, the row
--   space is exactly that of `rowList D ++ L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L111-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L111-L123

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_foldl_stepA (D : List (PivRow n)) (L : List (Vec n)) :
    spanL (rowList (L.foldl stepA D)) = spanL (rowList D ++ L) := by sorry
