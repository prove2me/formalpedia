-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
-- name    : WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/0e8f5714-9bdc-59c7-8b27-e0db105cdf99
-- title:
--   Existence of a dual pair for rational homomorphisms
-- statement:
--   Let $F$ be a field and $k$ a field equipped with an $F$-algebra structure, algebraically closed and with decidable equality; let $W_1,W_2$ be Weierstrass curves over $F$, both elliptic. Let $\rho$ be an additive group homomorphism from the points of the affine curve obtained by base change of $W_1$ to $k$ to those of the base change of $W_2$, and assume $\rho$ lies in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28), that is: either $\rho = 0$, or $\rho$ is rationally represented, meaning that there are bivariate polynomials $n_X,d_X,n_Y,d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ of the base change of $W_1$ with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ (after base change of coefficients) are nonzero and $\rho$ sends that point to the affine point with coordinates $n_X(x,y)/d_X(x,y)$, $n_Y(x,y)/d_Y(x,y)$. Assume further $\rho \neq 0$. Then there exist $\sigma$ in [`WeierstrassCurve.rationalHomSet k W₂ W₁`](def/WeierstrassCurve_RationalEnd.html#L28) and an integer $n > 0$ such that $\rho$ and $\sigma$ form a dual pair of exponent $n$: $\sigma(\rho(a)) = n \cdot a$ for all points $a$ of the base change of $W_1$, and $\rho(\sigma(b)) = n \cdot b$ for all points $b$ of the base change of $W_2$.
--
--   This is the existence of the dual isogeny $\hat{\rho}$, again defined over $F$, satisfying $\hat{\rho}\rho = [n]$ and $\rho\hat{\rho} = [n]$; only the existence of some positive exponent $n$ is asserted, not that $n$ is the degree of $\rho$. In this development it supplies the involution on rational homomorphism sets used in the Čerednik–Drinfeld part of the argument, where dual pairs of quotients of elliptic curves are matched with idele-theoretic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {ρ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hρ0 : ρ ≠ 0) : ∃ σ ∈ WeierstrassCurve.rationalHomSet k W₂ W₁, ∃ n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair ρ σ n := by sorry
