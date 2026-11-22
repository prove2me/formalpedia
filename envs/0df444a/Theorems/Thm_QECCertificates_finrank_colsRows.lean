-- Prove2me | Theorems.Thm_QECCertificates_finrank_colsRows
-- name    : QECCertificates.finrank_colsRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:19.956724+00:00
-- url     : https://prove2.me/theorems/78f02e21-2bd0-4b10-baad-c6c445f92c9b
-- title:
--   QECCertificates: finrank cols Rows
-- statement:
--   **The dimension of the tensor intersection**: the space of matrices with columns in
--   `U` and rows in `W` has dimension exactly $\dim U\cdot\dim W$.
--
--   This is the **only** nontrivial dimension input to the tensor formula
--   $k=k_1k_2+k_1^\top k_2^\top$ (the dimension of $U\otimes W$ in the language of matrices).
--   The proof goes through an explicit equivalence:
--
--   $$\{X:\mathrm{col}\,X\subseteq U,\ \mathrm{row}\,X\subseteq W\}\;\cong\;\mathrm{Fin}\,a\to W,
--   \qquad a=\dim U,$$
--
--   the forward map extracting coordinates with `wedge` and then taking rows, the backward map
--   forming `vee` from the `W`-combinations of the coefficient rows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L291-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L291-L370

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

theorem QECCertificates.finrank_colsRows (U : Submodule (ZMod 2) (Vec p)) (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W)
      = Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) W := by sorry
