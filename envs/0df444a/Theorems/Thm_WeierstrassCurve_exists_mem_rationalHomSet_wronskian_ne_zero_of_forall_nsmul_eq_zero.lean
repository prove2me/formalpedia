-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/5bb2f7b4-30ba-5a24-b4aa-c1985d3c3681
-- title:
--   Separable rational homomorphism onto a supersingular curve
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic a prime $p$, and let $X_0$ and $W$ be Weierstrass curves over $\kappa$ satisfying `IsElliptic`. Assume that the only point $P$ of the affine point group $X_0(\kappa)$ with $p \cdot P = 0$ is $P = 0$, and let $\chi$ be a homomorphism of additive groups from the points of the base change of $X_0$ to $\kappa$ to the points of the base change of $W$ to $\kappa$ which is nonzero and lies in `rationalHomSet`, i.e. which is either zero or rationally represented: there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $\kappa$ and a finite exceptional set $B \subseteq \kappa$ such that for every nonsingular affine point $(x,y)$ with $x \notin B$ both denominators are nonvanishing at $(x,y)$ and $\chi(x,y) = (n_X/d_X, n_Y/d_Y)$ evaluated there. Then there is a homomorphism $\rho$ from the points of $W$ to the points of $X_0$ (again over $\kappa$) belonging to `rationalHomSet` in the same sense, together with coprime polynomials $r, s \in \kappa[X]$ whose Wronskian $rs' - r's$ is nonzero and a finite set $B \subseteq \kappa$, such that for every nonsingular affine point $(x,y)$ of $W$ with $x \notin B$ the image $\rho(x,y)$ is an affine point $(x',y')$ with $x' \, s(x) = r(x)$.
--
--   The assertion is that a supersingular elliptic curve receives a separable isogeny from any curve admitting a nonzero rational homomorphism to it: the abscissa of $\rho$ is a rational function of the abscissa with nonvanishing Wronskian, which is the separability condition used throughout the project. It is invoked in the Cerednik–Drinfeld comparison of ideal classes of the endomorphism ring with isomorphism classes of supersingular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (hss : ∀ P : X₀.toAffine.Point, p • P = 0 → P = 0)
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0) :
    ∃ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, ∃ (r s : Polynomial κ) (B : Set κ),
      IsCoprime r s ∧ Polynomial.wronskian r s ≠ 0 ∧ B.Finite ∧
      ∀ (x y : κ) (h : (W.baseChange κ).toAffine.Nonsingular x y), x ∉ B →
        ∃ (x' y' : κ) (h' : (X₀.baseChange κ).toAffine.Nonsingular x' y'),
          ρ (.some x y h) = .some x' y' h' ∧ x' * s.eval x = r.eval x := by sorry
