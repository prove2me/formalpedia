-- Prove2me | Theorems.Thm_RibetLevelLowering_gramSnake_ker_and_coker_transfer
-- name    : RibetLevelLowering.gramSnake_ker_and_coker_transfer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/1669c863-67f7-5cfc-92d9-8df72ce4c827
-- title:
--   Snake-lemma transfer of kernel and cokernel for lattice pairings
-- statement:
--   Let $R$ be a commutative ring and let $Y,L,X,Y^d,L^d,X^d$ be $R$-modules. Given $R$-linear maps $\iota\colon Y\to L$ and $\delta\colon L\to X$ with $\delta(\iota y)=0$ for all $y$, a map $\sigma\colon X\to L$ and a scalar $\eta\in R$ with $\delta(\sigma x)=\eta\cdot x$ for all $x$, maps $\kappa^d\colon X^d\to L^d$ and $\rho^d\colon L^d\to Y^d$ such that $\rho^d$ is surjective, $\rho^d(\kappa^d\varphi)=0$ for all $\varphi$, and every $l\in L^d$ with $\rho^d l=0$ is of the form $\kappa^d\varphi$, and comparison maps $g_L\colon L\to L^d$ (injective), $g_X\colon X\to X^d$, $g_Y\colon Y\to Y^d$ satisfying $g_L(\sigma x)=\kappa^d(g_X x)$ for all $x$ and $g_Y y=\rho^d(g_L(\iota y))$ for all $y$, put $\Theta\colon L\to Y^d/\operatorname{range} g_Y$ for the composite of $g_L$, $\rho^d$ and the quotient map. Then four assertions hold: $\Theta$ vanishes on $\iota(Y)$; $\Theta$ vanishes on $\sigma(X)$; for every $u\in R$ such that every $\varphi\in X^d$ has $u\cdot\varphi$ in the image of $g_X$, and every $l\in L$ with $\Theta l=0$, there is $x_1\in X$ with $u\cdot\delta l=\eta\cdot x_1$; and for every $u\in R$ such that every $m\in L^d$ has $u\cdot m$ in the image of $g_L$, every class $\psi\in Y^d/\operatorname{range} g_Y$ satisfies $u\cdot\psi=\Theta l$ for some $l\in L$.
--
--   This is the module-theoretic (snake lemma) core behind Ribet's exact sequence $0\to K'\to X/\eta X\to\Psi'\to C'\to 0$ relating a character lattice, its old part and the component groups attached to the monodromy pairings: the two vanishing statements give the factorisation of $\Theta$, while the two divisibility statements bound its kernel and cokernel in terms of the annihilators of $X^d/g_X(X)$ and $L^d/g_L(L)$. It is used in the comparison of the rank of a Hecke-torsion component group with that of a quotient of character lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RibetLevelLowering_gramSnake_ker_and_coker_transfer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RibetLevelLowering.gramSnake_ker_and_coker_transfer
    {R : Type*} [CommRing R]
    {Y L X Yd Ld Xd : Type*}
    [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L] [AddCommGroup X] [Module R X]
    [AddCommGroup Yd] [Module R Yd] [AddCommGroup Ld] [Module R Ld] [AddCommGroup Xd] [Module R Xd]
    (ι : Y →ₗ[R] L) (δ : L →ₗ[R] X) (hδι : ∀ y : Y, δ (ι y) = 0)
    (σ : X →ₗ[R] L) (η : R) (hσ : ∀ x : X, δ (σ x) = η • x)
    (κd : Xd →ₗ[R] Ld) (ρd : Ld →ₗ[R] Yd) (hρd : Function.Surjective ρd)
    (hdc : ∀ φ : Xd, ρd (κd φ) = 0) (hexd : ∀ l : Ld, ρd l = 0 → ∃ φ : Xd, κd φ = l)
    (gL : L →ₗ[R] Ld) (hgL : Function.Injective gL) (gX : X →ₗ[R] Xd) (gY : Y →ₗ[R] Yd)
    (hsq : ∀ x : X, gL (σ x) = κd (gX x))
    (hres : ∀ y : Y, gY y = ρd (gL (ι y))) :
    let Θ : L →ₗ[R] (Yd ⧸ LinearMap.range gY) := (LinearMap.range gY).mkQ ∘ₗ ρd ∘ₗ gL
    (∀ y : Y, Θ (ι y) = 0) ∧
    (∀ x : X, Θ (σ x) = 0) ∧
    (∀ u : R, (∀ φ : Xd, ∃ x : X, u • φ = gX x) →
        ∀ l : L, Θ l = 0 → ∃ x₁ : X, u • δ l = η • x₁) ∧
    (∀ u : R, (∀ m : Ld, ∃ l : L, u • m = gL l) →
        ∀ ψ : Yd ⧸ LinearMap.range gY, ∃ l : L, u • ψ = Θ l) := by sorry
