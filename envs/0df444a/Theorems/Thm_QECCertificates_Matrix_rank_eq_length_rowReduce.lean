-- Prove2me | Theorems.Thm_QECCertificates_Matrix_rank_eq_length_rowReduce
-- name    : QECCertificates.Matrix.rank_eq_length_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:54.289254+00:00
-- url     : https://prove2.me/theorems/79ff21ad-5eaf-4add-8cb3-c12bf55d0b13
-- title:
--   Matrix: rank eq length row Reduce
-- statement:
--   **Rank certificate in matrix form**: reduce the rows of the parity-check matrix and
--   count them to obtain its rank.
--
--   `Matrix.rank` is the entry point through which the LeanQEC side of the distance reduction
--   reads a rank; this theorem lets the row reduction verified in this package take over that
--   reading directly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L224-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L224-L227

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

theorem QECCertificates.Matrix.rank_eq_length_rowReduce {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = (rowReduce (List.ofFn fun i => M i)).length := by sorry
