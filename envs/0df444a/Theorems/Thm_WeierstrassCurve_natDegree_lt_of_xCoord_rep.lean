-- Prove2me | Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
-- name    : WeierstrassCurve.natDegree_lt_of_xCoord_rep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6817d3fe-256c-568d-b016-c56523d45972
-- title:
--   Abscissa of an additive map has a pole at infinity
-- statement:
--   Let $k$ be an algebraically closed field with decidable equality, and let $W_1, W_2$ be Weierstrass curves over $k$, each assumed elliptic (invertible discriminant). Let $\alpha : W_1(k) \to W_2(k)$ be a homomorphism of additive groups between the groups of points of the associated affine curves, let $u, v \in k[X]$ be polynomials, and let $B \subseteq k$ be a subset. Assume: $u$ and $v$ are coprime in $k[X]$; $B$ is finite; and the abscissa of $\alpha$ is represented by $u/v$ away from $B$, in the sense that for every pair $(x,y) \in k^2$ together with a proof that $(x,y)$ is a nonsingular point of the affine curve $W_1$, and with $x \notin B$, there exist $x', y' \in k$ and a proof that $(x',y')$ is a nonsingular point of the affine curve $W_2$ such that $\alpha$ sends the affine point $(x,y)$ to the affine point $(x',y')$ and $x' \cdot v(x) = u(x)$. The conclusion is the inequality of natural degrees $\deg v < \deg u$. In particular the hypotheses force $u \neq 0$, and they cannot hold when $\alpha$ is the zero map, since every $x \in k$ is the abscissa of some point of $W_1$ while the hypothesis demands that the image be an affine point.
--
--   This is the normalisation statement that the rational function in $x$ computing the abscissa of a rational additive map of elliptic curves has a pole at infinity, so that, once written in lowest terms, the numerator degree is the degree of the map. It is used in the Čerednik–Drinfel'd material on rational homomorphisms and kernel ideals, where $\deg u$ serves as the degree of an endomorphism or isogeny. The proof evaluates at torsion points, using the division-polynomial formula $x(nP) = \Phi_n(x)/\Psi_n^2(x)$, the coprimality of $\Phi_n$ and $\Psi_n^2$, and the characterisation of $n$-torsion by the vanishing of $\psi_n$ (respectively of $\mathrm{pre}\Psi'_n$ for odd $n$).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natDegree_lt_of_xCoord_rep {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] (α : W₁.toAffine.Point →+ W₂.toAffine.Point) {u v : Polynomial k} {B : Set k} (huv : IsCoprime u v) (hB : B.Finite) (hα : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B → ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'), α (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' * v.eval x = u.eval x) : v.natDegree < u.natDegree := by sorry
