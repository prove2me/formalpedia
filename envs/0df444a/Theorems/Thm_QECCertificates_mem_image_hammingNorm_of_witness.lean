-- Prove2me | Theorems.Thm_QECCertificates_mem_image_hammingNorm_of_witness
-- name    : QECCertificates.mem_image_hammingNorm_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:19.305133+00:00
-- url     : https://prove2.me/theorems/45d5f0a4-00ff-4728-8b55-9d73ff37cf1a
-- title:
--   QECCertificates: mem image hamming Norm of witness
-- statement:
--   An undetectable nontrivial operator of weight `d₀` puts `d₀` among the values over
--   which the minimum is taken.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L133-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L133-L139

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_image_hammingNorm_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace)
    (hw : hammingNorm E = d₀) :
    d₀ ∈ Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset := by sorry
