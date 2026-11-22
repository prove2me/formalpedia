-- Prove2me | Theorems.Thm_QECCertificates_rowOf_wedge_mem
-- name    : QECCertificates.rowOf_wedge_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:09.69884+00:00
-- url     : https://prove2.me/theorems/1f2780c5-cd5a-4ad9-ad2a-73296219ee8e
-- title:
--   QECCertificates: row Of wedge mem
-- statement:
--   **The row condition pushes forward**: if the rows of `X` all lie in `W`, then so do the
--   rows of `wedge L X` (substituting the matrix representation `L x = Σ_i x_i · L(e_i)` into
--   the row sums of `wedge`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L243-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L243-L255

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

theorem QECCertificates.rowOf_wedge_mem {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} (hX : ∀ i, rowOf X i ∈ W) :
    ∀ k, rowOf (wedge L X) k ∈ W := by sorry
