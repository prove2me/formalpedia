-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/a6ee13ad-2b63-5196-848f-20a058c6fac7
-- title:
--   Rational factorisation of a homomorphism through a separable isogeny
-- statement:
--   Let $F$ be a field and $k$ an algebraically closed field extension of $F$, and let $W_1, W_2, W_3$ be elliptic Weierstrass curves over $F$. Let $\varphi$ be an additive map from the affine points of $W_1$ base changed to $k$ to those of $W_2$ base changed to $k$, and $\alpha$ an additive map from the points of $W_1$ over $k$ to those of $W_3$ over $k$ which lies in `rationalHomSet k W₁ W₃`, i.e. either $\alpha = 0$ or there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $F$ and a finite set $B_0 \subseteq k$ such that for every nonsingular point $(x,y)$ of $W_1$ over $k$ with $x \notin B_0$ the two denominators are nonzero at $(x,y)$ and $\alpha(x,y) = (n_X/d_X,\ n_Y/d_Y)$ evaluated there. Assume given univariate polynomials $P, S, N_0, N_1, R \in F[X]$ with $P$ monic, $\deg P = \deg S + 1$ and $P, S$ coprime, and a finite set $B \subseteq k$, such that for every nonsingular point $(x,y)$ of $W_1$ over $k$ with $x \notin B$ one has $S(x) \neq 0$, $R(x) \neq 0$ and $$\varphi(x,y) = \Bigl(\frac{P(x)}{S(x)},\ \frac{N_0(x) + N_1(x)\,y}{R(x)}\Bigr).$$ Assume finally that $\ker \varphi \subseteq \ker \alpha$, in the form that $\varphi(T) = 0$ implies $\alpha(T) = 0$ for every point $T$. Then there is an additive map $\beta$ in `rationalHomSet k W₂ W₃` (so $\beta = 0$, or $\beta$ is given off a finite set of abscissae by quotients of bivariate polynomials over $F$ as above) with $\alpha(T) = \beta(\varphi(T))$ for all $T$.
--
--   This is the universal property of a separable isogeny — factorisation of a homomorphism whose kernel contains that of the isogeny — in the explicit coordinate language of `rationalHomSet`, the point being that the factor $\beta$ is again given by rational functions defined over the base field $F$. It is used in the construction of quotient isogenies in Vélu form and in the identification of homomorphisms with prescribed cyclic kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
    {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k]
    (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    {φ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃)
    {P S N₀ N₁ R : F[X]} (hP : P.Monic) (hdeg : P.natDegree = S.natDegree + 1)
    (hcop : IsCoprime P S) {B : Set k} (hB : B.Finite)
    (hφ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
      ∃ h', φ (.some x y h) =
        .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h')
    (hker : ∀ T, φ T = 0 → α T = 0) :
    ∃ β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃, ∀ T, α T = β (φ T) := by sorry
