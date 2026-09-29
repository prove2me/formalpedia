-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul
-- name    : WeierstrassCurve.exists_comp_ne_comp_of_frobenius_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/00be0066-8388-5710-b7eb-1ea6cd827294
-- title:
--   Integral Frobenius forces a non-commuting pair of rational endomorphisms
-- statement:
--   Let $F$ be a finite field and let $k$ be an algebraically closed field which is an $F$-algebra and is algebraic over $F$. Let $W$ be a Weierstrass curve over $F$ which is elliptic, and write $(W⁄k).\mathrm{Point}$ for the group of points of its base change to $k$ in affine Weierstrass form. Let $\sigma : k \to k$ be an $F$-algebra map with $\sigma(x) = x^{\#F}$ for every $x \in k$, and let $a$ be an integer such that the map induced by $\sigma$ on points, `WeierstrassCurve.Affine.Point.map σ`, satisfies $\sigma_*(P) = a \cdot P$ for every $P \in (W⁄k).\mathrm{Point}$. Then there exist $\alpha$ and $\beta$, both in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28), with $\alpha \circ \beta \neq \beta \circ \alpha$ as additive self-maps of $(W⁄k).\mathrm{Point}$. Here an additive endomorphism $\gamma$ of $(W⁄k).\mathrm{Point}$ lies in `rationalHomSet k W W` when either $\gamma = 0$ or there are four bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $F$ and a finite set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ of $W⁄k$ with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ are non-zero and $\gamma$ sends $(x,y)$ to the affine point with coordinates $\bigl(n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y)\bigr)$.
--
--   This is Deuring's theorem that an elliptic curve over a finite field whose $q$-power Frobenius acts as an integer has non-commutative endomorphism ring, formulated for the ring of $F$-rational endomorphisms read on $k$-points. It feeds [`WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul`](thm.html#WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul), which extracts from it a pair of endomorphisms with prescribed anticommuting behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_comp_ne_comp_of_frobenius_eq_smul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_comp_ne_comp_of_frobenius_eq_smul {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ) (ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) : ∃ α ∈ WeierstrassCurve.rationalHomSet k W W, ∃ β ∈ WeierstrassCurve.rationalHomSet k W W, α.comp β ≠ β.comp α := by sorry
