-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
-- name    : WeierstrassCurve.Affine.Point.some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f367e5ab-83e0-5eb1-a1b7-4c30a56248a5
-- title:
--   Automorphism acting as ± 1 on ℓ-torsion, ℓ≡ 11 (mod 12)
-- statement:
--   Let $F$ be a field of characteristic $p$, with $p$ a prime, and let $W$ be a Weierstrass curve over $F$ which is elliptic (its discriminant is a unit). Let $C=(u;r,s,t)$ be a Weierstrass variable change over $F$ fixing the model, i.e. $C \cdot W = W$, and let $\ell$ be a prime natural number with $\ell \equiv 11 \pmod{12}$. Let $x,y \in F$ be such that $(x,y)$ is a nonsingular point of the affine curve attached to $W$, and suppose the corresponding point $P$ of the affine point group satisfies $\ell \cdot P = 0$. Suppose further that the transformed pair $\bigl(u^{-2}(x-r),\; u^{-3}(y - s(x-r) - t)\bigr)$ is again a nonsingular point of the same affine curve, so that it defines a point $P'$, and that $P' = n \cdot P$ for some integer $n$. Then $P' = P$ or $P' = -P$.
--
--   The statement isolates the standard fact that an automorphism of a Weierstrass model, whose action on a point of prime order $\ell$ is known to be multiplication by some integer, acts as $\pm 1$ when $\ell \equiv 11 \pmod{12}$, the congruence guaranteeing that $\gcd(24,\ell-1)=2$ while the automorphism group of the model has order dividing $24$. It is used in the counting of automorphism stabilisers at points of the modular curve with full level structure, in particular in the comparison of level automorphisms with rational automorphisms above the places $2$ and $3$, and in the analysis of the action on rigid data at such points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
    {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) (hC : C • W = W)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hℓP : ℓ • WeierstrassCurve.Affine.Point.some x y h = 0)
    (h' : W.toAffine.Nonsingular (((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r)) (((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)))
    (n : ℤ) (hn : WeierstrassCurve.Affine.Point.some _ _ h' = n • WeierstrassCurve.Affine.Point.some x y h) :
    WeierstrassCurve.Affine.Point.some _ _ h' = WeierstrassCurve.Affine.Point.some x y h ∨
      WeierstrassCurve.Affine.Point.some _ _ h' = -WeierstrassCurve.Affine.Point.some x y h := by sorry
