-- Prove2me | Theorems.Thm_QECCertificates_exists_leftInverse_of_linearIndependent
-- name    : QECCertificates.exists_leftInverse_of_linearIndependent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:57.976811+00:00
-- url     : https://prove2.me/theorems/5e7f5390-2216-43ad-8da6-d7b3417e8638
-- title:
--   QECCertificates: exists left Inverse of linear Independent
-- statement:
--   **Left inverse of an independent family**: when `u : Fin a → Vec p` is linearly
--   independent, there is a linear map `L` that reads the coefficients $c$ back from any
--   combination $\sum_k c_k u_k$.
--
--   The construction: the combination map $\varphi(c)=\sum_k c_k u_k$ is injective by
--   independence, and one takes a left inverse of it on the whole space
--   (`LinearMap.exists_leftInverse_of_injective`: over a vector space every injective linear
--   map has a left inverse).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L164-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L164-L181

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

theorem QECCertificates.exists_leftInverse_of_linearIndependent {u : Fin a → Vec p}
    (hu : LinearIndependent (ZMod 2) u) :
    ∃ L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2), ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c := by sorry
