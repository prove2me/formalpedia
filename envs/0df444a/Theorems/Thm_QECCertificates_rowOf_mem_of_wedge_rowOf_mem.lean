-- Prove2me | Theorems.Thm_QECCertificates_rowOf_mem_of_wedge_rowOf_mem
-- name    : QECCertificates.rowOf_mem_of_wedge_rowOf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:12.527101+00:00
-- url     : https://prove2.me/theorems/878a02f5-eb02-4792-bf3b-b59bab226832
-- title:
--   QECCertificates: row Of mem of wedge row Of mem
-- statement:
--   **The row condition pulls back**: if the rows of `wedge L X` all lie in `W` and the
--   columns of `X` all lie in `U`, then the rows of `X` all lie in `W` (using
--   `vee_wedge_of_coords` to write the rows of `X` as combinations of the rows of
--   `wedge L X`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L261-L275
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L261-L275

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

theorem QECCertificates.rowOf_mem_of_wedge_rowOf_mem {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)} {W : Submodule (ZMod 2) (Vec s)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s}
    (hX : ∀ j, colOf X j ∈ U) (hY : ∀ k, rowOf (wedge L X) k ∈ W) :
    ∀ i, rowOf X i ∈ W := by sorry
