-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
-- name    : WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f774dd44-ac9d-5997-b707-d4ac0bff3755
-- title:
--   Vélu's 2-isogeny: rationality, dual isogeny and factorisation
-- statement:
--   Let $K$ be an algebraically closed field in which $2 \neq 0$, let $W$ be a Weierstrass curve over $K$ that is elliptic, and let $x_0, y_0 \in K$ satisfy the affine Weierstrass equation of $W$ together with $\mathrm{veluGy}(x_0,y_0) = -(2y_0 + a_1x_0 + a_3) = 0$; write $W' = W.\mathrm{veluQuotient2}\,x_0\,y_0$ for the curve with the same $a_1,a_2,a_3$, with $a_4$ replaced by $a_4 - 5g$ and $a_6$ by $a_6 - b_2 g - 7x_0 g$, where $g = 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0$, and assume $\Delta_{W'} \neq 0$. Then there is an additive homomorphism $\pi$ from the group of affine points of $W$ to that of $W'$ whose underlying function is `veluPointMap2` — the point at infinity and every affine point with $x$-coordinate $x_0$ go to the point at infinity, and any other affine point $(x,y)$ goes to the point of $W'$ with Vélu's coordinates — such that: $\pi$ lies in $\mathrm{rationalHomSet}$, i.e. $\pi$ is zero or there are $n_X, d_X, n_Y, d_Y \in K[X][Y]$ and a finite $B \subseteq K$ with $d_X, d_Y$ nonvanishing at and $\pi$ given by $\bigl(n_X/d_X,\, n_Y/d_Y\bigr)$ on every nonsingular affine point $(x,y)$ with $x \notin B$; there is such a rational homomorphism $\pi' \colon W' \to W$ with $\pi' \circ \pi = 2\,\mathrm{id}$ and $\pi \circ \pi' = 2\,\mathrm{id}$; and for every elliptic Weierstrass curve $W_3$ over $K$ and every rational homomorphism $\alpha$ from the points of $W$ to those of $W_3$ vanishing at every $T$ with $\pi T = 0$, there is a rational homomorphism $\beta$ from $W'$ to $W_3$ with $\alpha = \beta \circ \pi$.
--
--   This packages the standard properties of the degree-$2$ isogeny with prescribed kernel $\{O, (x_0,y_0)\}$ constructed by Vélu's formulas: that it is given by rational functions off a finite set, that it admits a dual whose composites either way are multiplication by $2$, and the universal property of the quotient for rational homomorphisms killing its kernel. It supports the steps in which an elliptic curve with complex multiplication is replaced by a $2$-isogenous one, and is used in the modular-curve and Hecke-correspondence material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) : ∃ π : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point, ⇑π = WeierstrassCurve.veluPointMap2 h2 hQ hgy hΔ ∧ π ∈ WeierstrassCurve.rationalHomSet K W (W.veluQuotient2 x₀ y₀) ∧ (∃ π' ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W, π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _) ∧ ∀ (W₃ : WeierstrassCurve K) (_ : W₃.IsElliptic) (α : W.toAffine.Point →+ W₃.toAffine.Point), α ∈ WeierstrassCurve.rationalHomSet K W W₃ → (∀ T, π T = 0 → α T = 0) → ∃ β ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W₃, α = β.comp π := by sorry
