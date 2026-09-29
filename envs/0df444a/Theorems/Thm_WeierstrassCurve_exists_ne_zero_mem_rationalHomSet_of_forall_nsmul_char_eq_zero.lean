-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero
-- name    : WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c67914a8-6909-5fcb-a981-88fddcdfe9d5
-- title:
--   Supersingular elliptic curves in characteristic p are isogenous
-- statement:
--   Let $k$ be an algebraically closed field of prime characteristic $p$, and let $X_1, X_2$ be Weierstrass curves over $k$ which are elliptic (i.e. satisfy `IsElliptic`). Assume of each that it has no $k$-point of order $p$: every $P$ in the group of affine points $X_1$ with $p \cdot P = 0$ is the point at infinity, and likewise for $X_2$. The conclusion is that there exists an additive map $\beta$ from the points of the base change of $X_1$ to $k$ to the points of the base change of $X_2$ to $k$ (the base change along the identity algebra structure of $k$ over itself) which is nonzero and lies in [`WeierstrassCurve.rationalHomSet k X₁ X₂`](def/WeierstrassCurve_RationalEnd.html#L28), that is: either $\beta = 0$ or $\beta$ is rationally represented, meaning there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $k$ and a finite set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ with $x \notin B$ the denominators $d_X, d_Y$ do not vanish at $(x,y)$ and $\beta$ sends $(x,y)$ to the affine point $(n_X/d_X, n_Y/d_Y)$ evaluated at $(x,y)$. Since $\beta$ is required to be nonzero, the second alternative holds for it.
--
--   This is Deuring's theorem that the supersingular elliptic curves over an algebraically closed field of characteristic $p$ form a single isogeny class, with supersingularity expressed as the absence of $p$-torsion points and isogeny expressed as a nonzero additive map given off finitely many abscissae by one quadruple of polynomials. It supplies the supersingular branch in the analysis of the relevant endomorphism rings used in the Čerednik–Drinfeld results on class sets and supersingular places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_forall_nsmul_char_eq_zero {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (X₁ X₂ : WeierstrassCurve k) [X₁.IsElliptic] [X₂.IsElliptic] (h₁ : ∀ P : X₁.toAffine.Point, p • P = 0 → P = 0) (h₂ : ∀ P : X₂.toAffine.Point, p • P = 0 → P = 0) : ∃ β ∈ WeierstrassCurve.rationalHomSet k X₁ X₂, β ≠ 0 := by sorry
