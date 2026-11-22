-- Prove2me | Theorems.Thm_QECCertificates_lightCand_length_le
-- name    : QECCertificates.lightCand_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:34.859242+00:00
-- url     : https://prove2.me/theorems/41df8929-92f6-45b3-a749-6e3f4d2cf325
-- title:
--   QECCertificates: light Cand length le
-- statement:
--   **The size of the candidate space for the lower-bound certificate**: at most
--   $\sum_{k<d}\binom nk$.
--
--   This is the visible content of the certificate-complexity statement for the distance
--   decision: the candidate set is a weight-bounded enumeration, not $2^n$, and the
--   **enumeration length is exactly given by binomial coefficients** (`length_lightVecs`). For
--   fixed $d$ this is a polynomial of degree $d-1$ in $n$: 121 candidates at $n = 15, d = 3$,
--   against $32768$ for the full space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L238-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L238-L243

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.lightCand_length_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightCand M₁ M₂ d).length ≤ ∑ k ∈ Finset.range d, n.choose k := by sorry
