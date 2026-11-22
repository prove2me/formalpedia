-- Prove2me | Theorems.Thm_QECCertificates_hammingNorm_le_of_injective
-- name    : QECCertificates.hammingNorm_le_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:02.534821+00:00
-- url     : https://prove2.me/theorems/9c3ce30f-300a-404f-be62-659890270388
-- title:
--   QECCertificates: hamming Norm le of injective
-- statement:
--   Pulling a vector back along an injection does not increase its weight (the support
--   embeds under the injection).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L235-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L235-L244

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hammingNorm_le_of_injective {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (he : Function.Injective e) (v : β → ZMod 2) :
    hammingNorm (fun a => v (e a)) ≤ hammingNorm v := by sorry
