-- Prove2me | Theorems.Thm_QECCertificates_Matrix_rank_eq_finrank_rowSpace
-- name    : QECCertificates.Matrix.rank_eq_finrank_rowSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:44.197241+00:00
-- url     : https://prove2.me/theorems/23210732-c882-4de8-869c-14ebc30a54b6
-- title:
--   Matrix: rank eq finrank row Space
-- statement:
--   `Matrix.rank` of Mathlib is the dimension of the row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L213-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L213-L216

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

theorem QECCertificates.Matrix.rank_eq_finrank_rowSpace {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) M.certificateRowSpace := by sorry
