-- Prove2me | Theorems.Thm_QECCertificates_finrank_rowsSub
-- name    : QECCertificates.finrank_rowsSub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:54.870047+00:00
-- url     : https://prove2.me/theorems/4a113542-d2d0-427e-825c-6a0576df1f57
-- title:
--   QECCertificates: finrank rows Sub
-- statement:
--   **The dimension of the row-constrained space**:
--   $\dim\{X : \mathrm{row}\,X\subseteq W\} = p\cdot\dim W$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L138-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L138-L142

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}

theorem QECCertificates.finrank_rowsSub (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) (rowsSub (p := p) W) = p * Module.finrank (ZMod 2) W := by sorry
