-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/ea222334-e1a6-5cc4-b904-875703629304
-- title:
--   Vélu quotient with prescribed kernel and its universal property
-- statement:
--   Let $\kappa$ be an algebraically closed field with decidable equality, let $E$ be a Weierstrass curve over $\kappa$ that is elliptic, and let $H$ be an additive subgroup of the group of affine points of $E$ base changed to $\kappa$, subject to the hypothesis that the image in $\kappa$ of the natural number $\mathrm{Nat.card}\,H$ is nonzero (so $H$ is finite and its order is invertible in $\kappa$). The assertion is that there exist a Weierstrass curve $W$ over $\kappa$, together with a proof that $W$ is elliptic, and an additive homomorphism $\chi$ from the points of $E$ (base changed to $\kappa$) to the points of $W$ (base changed to $\kappa$) such that: $\chi$ lies in [`WeierstrassCurve.rationalHomSet κ E W`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. either $\chi = 0$ or $\chi$ is rationally represented, meaning there are bivariate polynomials $nX, dX, nY, dY$ over $\kappa$ and a finite set $B \subseteq \kappa$ such that for every nonsingular point $(x,y)$ of $E$ with $x \notin B$ the values of $dX$ and $dY$ at $(x,y)$ are nonzero and $\chi$ sends $(x,y)$ to the affine point with coordinates $nX(x,y)/dX(x,y)$ and $nY(x,y)/dY(x,y)$; moreover $\chi$ is surjective, $\ker \chi = H$, and $\chi$ is universal among such maps: for every elliptic Weierstrass curve $V$ over $\kappa$ and every additive homomorphism $\alpha$ from the points of $E$ to the points of $V$ lying in [`WeierstrassCurve.rationalHomSet κ E V`](def/WeierstrassCurve_RationalEnd.html#L28) with $H \le \ker \alpha$, there is a $\beta$ in [`WeierstrassCurve.rationalHomSet κ W V`](def/WeierstrassCurve_RationalEnd.html#L28) with $\alpha = \beta \circ \chi$.
--
--   This is the existence of the separable quotient isogeny $E \to E/H$ with prescribed finite kernel of order prime to the characteristic, in the shape given by Vélu's formulas, together with the universal property that a rational homomorphism killing $H$ factors through it; homomorphisms are recorded here as additive maps on $\kappa$-points that are given by rational functions outside a finite set of $x$-coordinates. It is used in the Čerednik–Drinfeld part of the development, where quotients by kernels attached to ideals and to pairs of isogenies are constructed and compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E : WeierstrassCurve κ) [E.IsElliptic]
    (H : AddSubgroup (E.baseChange κ).toAffine.Point) (hH : ((Nat.card H : ℕ) : κ) ≠ 0) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic)
      (χ : (E.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point),
      χ ∈ WeierstrassCurve.rationalHomSet κ E W ∧ Function.Surjective χ ∧ χ.ker = H ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → H ≤ α.ker →
        ∃ β ∈ WeierstrassCurve.rationalHomSet κ W V, α = β.comp χ := by sorry
