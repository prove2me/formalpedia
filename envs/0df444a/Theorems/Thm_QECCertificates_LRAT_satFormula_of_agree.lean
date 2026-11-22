-- Prove2me | Theorems.Thm_QECCertificates_LRAT_satFormula_of_agree
-- name    : QECCertificates.LRAT.satFormula_of_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:07.226543+00:00
-- url     : https://prove2.me/theorems/e6233729-9526-4b00-b16f-464ec2e4573d
-- title:
--   LRAT: sat Formula of agree
-- statement:
--   A set of clauses is preserved between assignments that agree below the threshold.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1015-L1018
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1015-L1018

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.satFormula_of_agree {σ τ : Assign} {F : CNF} {c : Nat}
    (h : ∀ t, t < c → τ t = σ t) (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < c)
    (hσ : SatFormula σ F) : SatFormula τ F := by sorry
