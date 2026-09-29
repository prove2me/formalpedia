-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
-- name    : WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/aac5c61c-3020-50b1-99a4-921997d58634
-- title:
--   Supersingular Frobenius: a power acts as an integer
-- statement:
--   Let $F$ be a finite field of characteristic $p$ ($p$ a prime), let $k$ be an algebraically closed field that is an $F$-algebra and algebraic over $F$, and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $\sigma : k \to k$ be an $F$-algebra endomorphism of $k$ which is the $q$-power map, $\sigma x = x^{q}$ with $q = \#F$, for every $x \in k$, and write $\pi$ for the induced endomorphism `WeierstrassCurve.Affine.Point.map` $\sigma$ of the group $(W\!\!\restriction_k)$`.Point` of affine points of the base change of $W$ to $k$ (points $(x,y)$ on the affine Weierstrass equation together with the point at infinity). Assume that $W$ has no $k$-point of order exactly $p$: every $P$ in $(W\!\!\restriction_k)$`.Point` with $p \cdot P = 0$ satisfies $P = 0$. Then there exist a positive natural number $n$ and an integer $a$ such that the $n$-fold iterate of $\pi$ is multiplication by $a$ on all of $(W\!\!\restriction_k)$`.Point`, that is, $\pi^{n}(P) = a \cdot P$ for every point $P$.
--
--   This is the classical fact, going back to Deuring's theory of supersingular elliptic curves, that for a supersingular curve over a finite field some positive power of the $q$-power Frobenius is multiplication by an integer (equivalently $\pi_q/\sqrt q$ is a root of unity), with supersingularity taken here in the form that there is no $k$-point of order $p$. It feeds the analysis of the endomorphism ring of a supersingular curve, being cited by [`WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero), [`WeierstrassCurve.exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv`](thm.html#WeierstrassCurve.exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv) and [`WeierstrassCurve.free_and_finrank_rationalEndSubring_eq_four`](thm.html#WeierstrassCurve.free_and_finrank_rationalEndSubring_eq_four).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (h : ∀ P : (W⁄k).Point, p • P = 0 → P = 0) : ∃ n : ℕ, 0 < n ∧ ∃ a : ℤ, ∀ P : (W⁄k).Point, (WeierstrassCurve.Affine.Point.map (W' := W) σ)^[n] P = a • P := by sorry
