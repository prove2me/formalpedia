-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_eq_false_iff_dotProduct
-- name    : QECCertificates.LRAT.dotS_eq_false_iff_dotProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:42.208526+00:00
-- url     : https://prove2.me/theorems/82e98653-1701-4c2d-a4d1-c68c9358153c
-- title:
--   LRAT: dot S eq false iff dot Product
-- statement:
--   **Bridge 2**: `dotS` reports false if and only if the vector read out is orthogonal to the
--   support
--   vector.
--
--   `hr` requires the indices of the support list to lie within the code length (the encoder's output
--   satisfies this) and `hrn` requires no duplicates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L147-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L147-L151

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_eq_false_iff_dotProduct (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    dotS σ r = false ↔ (rowOf n r) ⬝ᵥ (vecOf σ n) = 0 := by sorry
