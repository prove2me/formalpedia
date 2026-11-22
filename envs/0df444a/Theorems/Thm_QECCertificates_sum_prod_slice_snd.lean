-- Prove2me | Theorems.Thm_QECCertificates_sum_prod_slice_snd
-- name    : QECCertificates.sum_prod_slice_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:09.926333+00:00
-- url     : https://prove2.me/theorems/f766a5e9-97ce-4bec-89d0-7cc6b5615cda
-- title:
--   QECCertificates: sum prod slice snd
-- statement:
--   "Take one column" on a product index: `Σ_{a,b} A a · [j = b] · F a b = Σ_a A a · F a j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L94-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L94-L107

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

theorem QECCertificates.sum_prod_slice_snd {m k : ℕ} (A : Fin m → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (j : Fin k) :
    (∑ p : Fin m × Fin k, A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)
      = ∑ a, A a * F a j := by sorry
