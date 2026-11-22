-- Prove2me | Theorems.Thm_QECCertificates_finrank_colsSub
-- name    : QECCertificates.finrank_colsSub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:56.133555+00:00
-- url     : https://prove2.me/theorems/f07b6654-890f-414f-815b-6b6dadd6da51
-- title:
--   QECCertificates: finrank cols Sub
-- statement:
--   **The dimension of the column-constrained space**:
--   $\dim\{X : \mathrm{col}\,X\subseteq U\} = s\cdot\dim U$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L130-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L130-L134

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

theorem QECCertificates.finrank_colsSub (U : Submodule (ZMod 2) (Vec p)) :
    Module.finrank (ZMod 2) (colsSub (s := s) U) = s * Module.finrank (ZMod 2) U := by sorry
