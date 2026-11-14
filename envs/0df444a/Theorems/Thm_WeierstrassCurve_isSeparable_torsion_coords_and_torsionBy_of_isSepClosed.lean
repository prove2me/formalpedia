-- Prove2me | Theorems.Thm_WeierstrassCurve_isSeparable_torsion_coords_and_torsionBy_of_isSepClosed
-- name    : WeierstrassCurve.isSeparable_torsion_coords_and_torsionBy_of_isSepClosed
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T00:57:33.871255+00:00
-- url     : https://prove2.me/theorems/ca6d11ae-fbd7-4178-963d-63da3793771d
-- title:
--   Torsion of an elliptic curve over a separably closed field: $E(L)[n] \cong (\mathbb Z/n)^2$ when $n \ne 0$ in $K$, and $n$-torsion points have coordinates separable over $K$
-- statement:
--   Let $K$ be a field, let $E$ be an elliptic curve over $K$ given by a Weierstrass equation, and let $n$ be a natural number with $n \ne 0$ in $K$ (so $n \ge 1$ and the characteristic of $K$ does not divide $n$). Let $L$ be a field extension of $K$ and write
--
--   $$E(L)[n] = \{P \in E(L) : nP = 0\}.$$
--
--   Then:
--
--   1. for every affine point $P = (x, y) \in E(L)$ with $nP = 0$, both coordinates $x$ and $y$ are separable over $K$;
--   2. if $L$ is separably closed, then
--
--   $$\# E(L)[n] = n^2 \qquad\text{and}\qquad E(L)[n] \cong \mathbb Z/n\mathbb Z \times \mathbb Z/n\mathbb Z.$$
--
--   Taking $L = K$ gives the statement for an elliptic curve over a separably closed field $K$.
--
--   Role: the structure theorem $E[n] \cong (\mathbb Z/n)^2$ for $n$ prime to the characteristic is usually stated over an algebraic closure $\bar K$. Over an imperfect field of characteristic $p$ the separable closure $K^{\mathrm{sep}}$ is strictly smaller than $\bar K$; part 1 shows that every $n$-torsion point is nevertheless defined over $K^{\mathrm{sep}}$, so $E(K^{\mathrm{sep}})[n] = E(\bar K)[n] \cong (\mathbb Z/n)^2$ and the Galois group $\mathrm{Gal}(K^{\mathrm{sep}}/K)$ acts on it. This is the setting of the mod-$n$ Galois representation and of the $\ell$-adic Tate module of $E$.
--
--   **Formalization Note**: $E$ is `W : WeierstrassCurve K` with `[W.IsElliptic]` (invertible discriminant), and $E(L)$ is `(W.baseChange L).toAffine.Point`, the group of points of the base change, whose zero is the point at infinity; the affine point $(x, y)$ is `Point.some x y h`, where `h` says that $(x, y)$ is a nonsingular solution. $E(L)[n]$ is `Submodule.torsionBy ℤ _ n`, the subgroup of points killed by $n$. `IsSeparable K x` says that the minimal polynomial of $x$ over $K$ is separable; in particular $x$ is algebraic over $K$. Part 1 holds for every extension $L$, with no closedness assumption. Part 2 assumes `IsSepClosed L`; a separably closed field $K$ is an extension of itself through `Algebra.id`.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Corollary III.6.4(b) and Section III.7; L. C. Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., CRC Press 2008, Theorem 3.2 and Section 3.2

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.isSeparable_torsion_coords_and_torsionBy_of_isSepClosed
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    (∀ {x y : L} (h : (W.baseChange L).toAffine.Nonsingular x y),
        n • (WeierstrassCurve.Affine.Point.some x y h : (W.baseChange L).toAffine.Point) = 0 →
          IsSeparable K x ∧ IsSeparable K y) ∧
      (IsSepClosed L →
        Nat.card (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n) = n ^ 2 ∧
          Nonempty (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n ≃+ ZMod n × ZMod n)) := by sorry
