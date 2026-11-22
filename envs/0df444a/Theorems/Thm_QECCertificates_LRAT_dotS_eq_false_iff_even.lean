-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_eq_false_iff_even
-- name    : QECCertificates.LRAT.dotS_eq_false_iff_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:35.811878+00:00
-- url     : https://prove2.me/theorems/36139e3a-dd02-4229-ba07-72ab0a5db64e
-- title:
--   LRAT: dot S eq false iff even
-- statement:
--   `dotS` is parity: the XOR dot product is false if and only if the number of true entries is
--   even.
--
--   This step does not need the support list to have no duplicates, since the XOR and the count each
--   take multiplicities into account.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L91-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L91-L97

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_eq_false_iff_even (σ : Assign) (r : List Nat) :
    dotS σ r = false ↔ Even (cntS σ r) := by sorry
