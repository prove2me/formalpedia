-- Prove2me | Theorems.Thm_QECCertificates_DualWitness_not_mem_rowSpace
-- name    : QECCertificates.DualWitness.not_mem_rowSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:43.153458+00:00
-- url     : https://prove2.me/theorems/a7feb873-c2af-4f97-917b-110b3dd24dec
-- title:
--   Dual Witness: not mem row Space
-- statement:
--   **Certificate soundness**: holding a dual witness proves that `E` is not in the
--   parity-check row space, hence that it is a logical operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L90-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L90-L92

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.DualWitness.not_mem_rowSpace {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {E : Vec n}
    (hw : DualWitness H E) : E ∉ H.certificateRowSpace := by sorry
