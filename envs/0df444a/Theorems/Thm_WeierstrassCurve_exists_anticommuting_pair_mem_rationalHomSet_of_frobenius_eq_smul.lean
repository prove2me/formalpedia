-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
-- name    : WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c477e61e-e7db-5ead-9203-3f2f29f5804e
-- title:
--   Anticommuting pair of rational endomorphisms when Frobenius is an integer
-- statement:
--   Let $F$ be a finite field with $q = \#F$ elements, let $k$ be an algebraically closed field that is an $F$-algebra and algebraic over $F$, and let $W$ be a Weierstrass curve over $F$ which is elliptic. Let $\sigma : k \to k$ be an $F$-algebra map with $\sigma(x) = x^{q}$ for all $x \in k$, and let $a \in \mathbb{Z}$ be such that applying $\sigma$ coordinatewise to the points of the base-changed curve acts as multiplication by $a$: $\sigma_*P = a \cdot P$ for every $P \in (W_{/k})(k)$. The conclusion asserts the existence of two additive endomorphisms $i, j$ of the group $(W_{/k})(k)$, each lying in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28) — that is, each either zero or rationally represented, meaning that there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $F$ and a finite set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ of $W_{/k}$ with $x \notin B$ the denominators do not vanish at $(x,y)$ and the map sends $(x,y)$ to $\bigl(n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y)\bigr)$ — together with nonzero integers $u, v$ such that $i(i(P)) = u \cdot P$ and $j(j(P)) = v \cdot P$ for all $P$, and $i(j(P)) = -\,j(i(P))$ for all $P$.
--
--   This is Deuring's structure theorem in the case where the $q$-power Frobenius acts as an integer (so that the curve is supersingular and all geometric endomorphisms are $F$-rational), recorded in a basis-free elementwise form: the rational endomorphism ring contains standard quaternion generators $i, j$ with nonzero integer squares that anticommute. It feeds the computation of the rational endomorphism ring as a free module of rank four, the quadratic relation satisfied by a single rational endomorphism, and the description of Frobenius-equivariant endomorphisms of the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ) (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) : ∃ i ∈ WeierstrassCurve.rationalHomSet k W W, ∃ j ∈ WeierstrassCurve.rationalHomSet k W W, ∃ u v : ℤ, u ≠ 0 ∧ v ≠ 0 ∧ (∀ P, i (i P) = u • P) ∧ (∀ P, j (j P) = v • P) ∧ (∀ P, i (j P) = -(j (i P))) := by sorry
