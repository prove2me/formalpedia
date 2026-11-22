-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_append
-- name    : QECCertificates.LRAT.dotS_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:41.297917+00:00
-- url     : https://prove2.me/theorems/b86bb447-5991-4e64-9a93-d97e3d6139de
-- title:
--   LRAT: dot S append
-- statement:
--   The concatenation law: the dot product is additive under concatenation of support
--   sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L57-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L57-L61

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_append (σ : Assign) (s t : List Nat) :
    dotS σ (s ++ t) = (dotS σ s ^^ dotS σ t) := by sorry
