-- Prove2me | Theorems.Thm_QECCertificates_lp_orthogonal
-- name    : QECCertificates.lp_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:42.154781+00:00
-- url     : https://prove2.me/theorems/8183b401-6848-4469-a427-7d677dcc56d4
-- title:
--   QECCertificates: lp orthogonal
-- statement:
--   **CSS compatibility of the lifted product**: $H_X H_Z^{\top} = 0$, for **any** seeds $A, B$.
--
--   Entrywise, the left and the right block each collapse to a single sum (`Finset.sum_eq_single`
--       removes
--   the Kronecker $\delta$ factor), and the two summands are $(L(A_{ij})\cdot
--       R(B_{st}))(\sigma,\sigma')$
--   and $(R(B_{st})\cdot L(A_{ij}))(\sigma,\sigma')$, which are equal by `leftMulMat_mul_rightMulMat`
--       and
--   therefore add to zero over $\mathbb{F}_2$. **No enumeration is involved.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L258-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L258-L305

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp_orthogonal [Fintype G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    lpHX A B * (lpHZ A B).transpose = 0 := by sorry
