-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_natDegree_parallelogram_law
-- name    : WeierstrassCurve.Affine.Point.natDegree_parallelogram_law
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d8d46a03-b886-547a-a5fe-43d7385287f3
-- title:
--   Parallelogram law for degrees of abscissa maps
-- statement:
--   Let $k$ be an algebraically closed field with decidable equality, and let $W$ be a Weierstrass curve over $k$ which is elliptic (invertible discriminant). Let $S \subseteq k$ be a finite set and let $u,v,s,t,u_1,v_1,u_2,v_2 \in k[X]$ satisfy: $u,v$ coprime, $s,t$ coprime, $u_1,v_1$ coprime, $u_2,v_2$ coprime, with $u \ne 0$, $v \ne 0$, $t \ne 0$, $v_1 \ne 0$, $v_2 \ne 0$, and the degree conditions $\deg v \le \deg u$ and $\deg t < \deg s$. Assume that for every $x \in k$ outside $S$ there are field elements $x_a,y_a,x_b,y_b,x_p,y_p,x_m,y_m$ which are nonsingular points of the affine curve $W$, such that, in the group of affine points of $W$ (with point at infinity), $(x_a,y_a) + (x_b,y_b) = (x_p,y_p)$ and $(x_a,y_a) - (x_b,y_b) = (x_m,y_m)$, and such that $x_a\,v(x) = u(x)$, $x_b\,t(x) = s(x)$, $x_p\,v_1(x) = u_1(x)$, $x_m\,v_2(x) = u_2(x)$. Then $u_1 \ne 0$, $u_2 \ne 0$, $$\deg u_1 + \deg u_2 = 2(\deg u + \deg s), \qquad \deg v_1 + \deg v_2 = 2\deg(ut - sv),$$ all degrees being `natDegree`.
--
--   This is the second-difference step in Manin's elementary treatment of the Hasse bound: writing $d$ for the degree of the numerator of an abscissa map, it expresses $d(A+B) + d(A-B) = 2d(A) + 2d(B)$ for families of points parametrised by $x$, in a form valid in every characteristic. It feeds the degree recursion for the kernel degrees of $[m] - \pi$ with $\pi$ the Frobenius endomorphism, and the construction of dual isogenies on the ring of rational endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_natDegree_parallelogram_law.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.natDegree_parallelogram_law {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (W : WeierstrassCurve k) [W.IsElliptic] {S : Set k} (hS : S.Finite) {u v s t u₁ v₁ u₂ v₂ : Polynomial k} (huv : IsCoprime u v) (hst : IsCoprime s t) (huv₁ : IsCoprime u₁ v₁) (huv₂ : IsCoprime u₂ v₂) (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hvu : v.natDegree ≤ u.natDegree) (hts : t.natDegree < s.natDegree) (H : ∀ x : k, x ∉ S → ∃ (xa ya xb yb xp yp xm ym : k) (ha : W.toAffine.Nonsingular xa ya) (hb : W.toAffine.Nonsingular xb yb) (hp : W.toAffine.Nonsingular xp yp) (hm : W.toAffine.Nonsingular xm ym), Point.some xa ya ha + Point.some xb yb hb = Point.some xp yp hp ∧ Point.some xa ya ha - Point.some xb yb hb = Point.some xm ym hm ∧ xa * v.eval x = u.eval x ∧ xb * t.eval x = s.eval x ∧ xp * v₁.eval x = u₁.eval x ∧ xm * v₂.eval x = u₂.eval x) : u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₁.natDegree + u₂.natDegree = 2 * (u.natDegree + s.natDegree) ∧ v₁.natDegree + v₂.natDegree = 2 * (u * t - s * v).natDegree := by sorry
