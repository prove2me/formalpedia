-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotProduct_rowOf_vecOf
-- name    : QECCertificates.LRAT.dotProduct_rowOf_vecOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:33.923015+00:00
-- url     : https://prove2.me/theorems/3bc798b8-e496-416f-9a62-189e3bff4eb4
-- title:
--   LRAT: dot Product row Of vec Of
-- statement:
--   Expansion of the product: the entrywise product of `rowOf` and `vecOf` is an indicator
--   function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L105-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L105-L111

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotProduct_rowOf_vecOf (σ : Assign) (n : ℕ) (r : List Nat) :
    (rowOf n r) ⬝ᵥ (vecOf σ n)
      = ∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0) := by sorry
