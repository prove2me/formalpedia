-- Prove2me | Theorems.Thm_QECCertificates_eq_zero_of_mem_spanL_of_piv_eq_zero
-- name    : QECCertificates.eq_zero_of_mem_spanL_of_piv_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:03.657665+00:00
-- url     : https://prove2.me/theorems/c23ab472-1dbf-4d8e-ace1-f6ee6cccd193
-- title:
--   QECCertificates: eq zero of mem span L of piv eq zero
-- statement:
--   **In echelon form, all pivot columns zero implies zero**: if `w` lies in the span of
--   `rowList D` and is 0 on **every** pivot column of `D`, then `w = 0`.
--
--   The argument: take a coefficient representation `w = Σ cᵢ rᵢ` and let `j` be the **least**
--   index with `cⱼ ≠ 0`. Evaluating on `pⱼ`, the terms with `i > j` vanish by `EchPair` and
--   those with `i < j` have coefficient 0, so `w pⱼ = cⱼ ≠ 0`, contradicting the hypothesis.
--   This is exactly the part that the symmetry condition (R2) of `IsReduced` used to carry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L388-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L388-L436

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_zero_of_mem_spanL_of_piv_eq_zero {D : List (PivRow n)} (h1 : EchSelf D)
    (h2 : EchPair D) {w : Vec n} (hw : w ∈ spanL (rowList D))
    (h0 : ∀ i : Fin D.length, w (D.get i).2 = 0) : w = 0 := by sorry
