-- Prove2me | Theorems.Thm_QECCertificates_sum_prod_slice_fst
-- name    : QECCertificates.sum_prod_slice_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:13.386711+00:00
-- url     : https://prove2.me/theorems/77064731-aa5a-409d-997f-e5f61c3428f4
-- title:
--   QECCertificates: sum prod slice fst
-- statement:
--   "Take one row" on a product index: `Σ_{a,b} [i = a] · B b · F a b = Σ_b B b · F i b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L110-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L110-L123

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

theorem QECCertificates.sum_prod_slice_fst {m k : ℕ} (B : Fin k → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (i : Fin m) :
    (∑ p : Fin m × Fin k, (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)
      = ∑ b, B b * F i b := by sorry
