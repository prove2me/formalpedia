-- Prove2me | Theorems.Thm_QECCertificates_length_lightVecs
-- name    : QECCertificates.length_lightVecs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:22.292483+00:00
-- url     : https://prove2.me/theorems/502fead6-dced-49ee-9273-36e032fad5c8
-- title:
--   QECCertificates: length light Vecs
-- statement:
--   **The exact length of the enumeration**: `lightVecs n w` has exactly
--   $\sum_{k \le w}\binom nk$ elements.
--
--   This is the concrete content of the size of a distance-decision certificate: since a lower
--   bound only has to exclude operators of weight $< d$, taking $w = d-1$ makes the
--   **candidate space exactly $\sum_{k<d}\binom nk$**, a polynomial of degree $d-1$ in $n$
--   rather than the $2^n$ of the full space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L299-L326
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L299-L326

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.length_lightVecs : ∀ (n w : ℕ),
    (lightVecs n w).length = ∑ k ∈ Finset.range (w + 1), n.choose k := by sorry
