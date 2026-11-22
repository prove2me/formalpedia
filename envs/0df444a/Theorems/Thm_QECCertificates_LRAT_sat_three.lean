-- Prove2me | Theorems.Thm_QECCertificates_LRAT_sat_three
-- name    : QECCertificates.LRAT.sat_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:23.345546+00:00
-- url     : https://prove2.me/theorems/455c7ed0-775b-41f3-993c-82569345a03a
-- title:
--   LRAT: sat three
-- statement:
--   The semantics of a three-literal clause.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L93-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L93-L100

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.sat_three {σ : Assign} {a b c : Lit} (h : SatClause σ [a, b, c]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 ∨ σ c.1 = c.2 := by sorry
