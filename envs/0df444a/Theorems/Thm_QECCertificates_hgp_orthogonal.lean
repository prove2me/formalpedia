-- Prove2me | Theorems.Thm_QECCertificates_hgp_orthogonal
-- name    : QECCertificates.hgp_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:38.174798+00:00
-- url     : https://prove2.me/theorems/04fc05ec-826f-4679-80e1-2a14bf0348c6
-- title:
--   QECCertificates: hgp orthogonal
-- statement:
--   **CSS compatibility of the HGP (structural theorem)**: $H_X H_Z^\top = 0$ for arbitrary
--   $H_1, H_2$.
--
--   The two blocks contribute $(H_1 \otimes I)(I \otimes H_2)^\top = H_1 \otimes H_2^\top$ and
--   $(I \otimes H_2^\top)(H_1^\top \otimes I)^\top = H_1 \otimes H_2^\top$ respectively, that is,
--   the same matrix added to itself, which is zero over GF(2). The two `Finset.sum_eq_single`
--   applications in the proof are this tensor identity at the entrywise level: each product
--   $H_1\, i\, a \cdot H_2\, d\, j$ is contributed exactly once, by $(a, j)$ on the left half and
--   by $(i, d)$ on the right half.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L104-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean#L104-L144

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgp_orthogonal (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    hgpHX H₁ H₂ * (hgpHZ H₁ H₂).transpose = 0 := by sorry
