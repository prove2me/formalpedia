-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_echelonFrom_eq_zero_of_mem_spanL
-- name    : QECCertificates.reduceAgainst_echelonFrom_eq_zero_of_mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:09.632698+00:00
-- url     : https://prove2.me/theorems/85d6b4ec-b818-43d4-be0c-773845d24d93
-- title:
--   QECCertificates: reduce Against echelon From eq zero of mem span L
-- statement:
--   **The reduction vanishes exactly on the row space (echelon backend)**: the output of
--   `echelonFrom` annihilates the span of the original list of rows.
--
--   This is parallel to `reduceAgainst_eq_zero_of_mem_spanL` in `GF2/Membership.lean`, the
--   `IsReduced` version, but the hypotheses here use only `EchSelf` and `EchPair`; the step that
--   the RREF used to carry is supplied by `eq_zero_of_mem_spanL_of_piv_eq_zero`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L444-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L444-L457

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_echelonFrom_eq_zero_of_mem_spanL {L : List (Vec n)} {v : Vec n}
    (hv : v ∈ spanL L) : reduceAgainst (echelonFrom L) v = 0 := by sorry
