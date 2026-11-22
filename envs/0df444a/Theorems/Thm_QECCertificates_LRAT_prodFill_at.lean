-- Prove2me | Theorems.Thm_QECCertificates_LRAT_prodFill_at
-- name    : QECCertificates.LRAT.prodFill_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:03.374683+00:00
-- url     : https://prove2.me/theorems/cc523530-89c6-4c8c-b63b-8802f74ac44a
-- title:
--   LRAT: prod Fill at
-- statement:
--   The value at a product variable is the conjunction of the two factors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L384-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L384-L388

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.prodFill_at (σ : Assign) (c n j : Nat) (hj : j < n) :
    prodFill σ c n (c + j) = (σ j && σ (n + j)) := by sorry
