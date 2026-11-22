-- Prove2me | Theorems.Thm_QECCertificates_Matrix_rank_eq_rankEchelon
-- name    : QECCertificates.Matrix.rank_eq_rankEchelon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:02.380681+00:00
-- url     : https://prove2.me/theorems/c80471e9-ccea-4eaf-8d1a-8649c7c85387
-- title:
--   Matrix: rank eq rank Echelon
-- statement:
--   The interface in matrix form: the rank of a parity-check matrix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L362-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L362-L364

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.Matrix.rank_eq_rankEchelon {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = rankEchelon (List.ofFn fun i => M i) := by sorry
