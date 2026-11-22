-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_stepA
-- name    : QECCertificates.spanL_rowList_stepA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:35.720354+00:00
-- url     : https://prove2.me/theorems/c9f2de23-2671-4e60-bb36-7544fb94a8d7
-- title:
--   QECCertificates: span L row List step A
-- statement:
--   Appending spans the same row space as appending the original, unreduced row: the
--   reduced vector lies in the original row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L91-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L91-L107

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_stepA (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (stepA D v)) = spanL (rowList D ++ [v]) := by sorry
