-- Prove2me | Theorems.Thm_QECCertificates_minWeight_le_of_witness
-- name    : QECCertificates.minWeight_le_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:21.613534+00:00
-- url     : https://prove2.me/theorems/33509ddb-e55a-4006-ab50-d0a51876c2eb
-- title:
--   QECCertificates: min Weight le of witness
-- statement:
--   **The upper-bound theorem**: if an undetectable nontrivial operator of weight `d₀`
--   exists, then the code distance is at most `d₀`.
--
--   This is the witness upper bound: the certificate is a concrete low-weight logical
--   operator, and the kernel only has to check the three assertions `E ∈ ker M₁`,
--   `E ∉ certificateRowSpace M₂` and `hammingNorm E = d₀`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L147-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L147-L168

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.minWeight_le_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace)
    (hw : hammingNorm E = d₀) :
    minWeightKernelOutsideRowSpace M₁ M₂ ≤ d₀ := by sorry
