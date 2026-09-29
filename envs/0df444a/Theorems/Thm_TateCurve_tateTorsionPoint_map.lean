-- Prove2me | Theorems.Thm_TateCurve_tateTorsionPoint_map
-- name    : TateCurve.tateTorsionPoint_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/33ed40d1-2b83-5e75-bf08-2f336d6b1981
-- title:
--   Isometric q-fixing endomorphisms act triangularly on Tate torsion points
-- statement:
--   Let $K$ be a nontrivially normed, ultrametric, complete field of characteristic zero which is algebraically closed, and let $q,\zeta,t\in K$ with $q\neq 0$ and $\|q\|<1$. Let $p$ be a prime with $p\ge 5$, let $\zeta$ be a primitive $p$-th root of unity and let $t^{p}=q$. Let $\sigma:K\to K$ be a ring homomorphism which is an isometry, with $\sigma q=q$, and suppose natural numbers $e,c$ satisfy $\sigma\zeta=\zeta^{e}$ and $\sigma t=\zeta^{c}t$. Let $i,j<p$ with $(i,j)\neq(0,0)$. Write $X(u)=\bigl(\sum_{n\in\mathbb Z}\mathrm{xfun}(q^{n}u)\bigr)-2s_{1}(q)$ and $Y(u)=\bigl(\sum_{n\in\mathbb Z}\mathrm{yfun}(q^{n}u)\bigr)+s_{1}(q)$ for the Tate coordinate series, and let $E_{q}$ be the Weierstrass curve $\langle 1,0,0,a_{4}(q),a_{6}(q)\rangle$ over $K$. Assuming that the affine equation of $E_{q}$ is nonsingular at the pair $\bigl(\sigma X(\zeta^{i}t^{j}),\sigma Y(\zeta^{i}t^{j})\bigr)$, the conclusion is that the affine point of $E_{q}$ with these coordinates equals [`TateCurve.tateTorsionPoint`](def/TateCurve_TorsionParametrization.html#L905) at the index pair $\bigl((ei+cj)\bmod p,\;j\bigr)$, i.e. the point with coordinates $X(\zeta^{(ei+cj)\bmod p}t^{j})$, $Y(\zeta^{(ei+cj)\bmod p}t^{j})$.
--
--   This is the equivariance of the Tate parametrisation of $E_{q}[p]$ under an isometric endomorphism of $K$ fixing $q$: in the basis given by the indices $(i,j)$ the action is upper triangular, the second index $j$ being preserved. It is used in the construction of the $\zeta$-$t$ parametrisation of the $p$-torsion of a Tate curve over an algebraic closure of $\mathbb Q_{p}$, where the action of the local Galois group is read off in this triangular form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_tateTorsionPoint_map.lean

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in

theorem TateCurve.tateTorsionPoint_map
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (σ : K →+* K) (hσ : Isometry ⇑σ) (hσq : σ q = q)
    {e c : ℕ} (hσζ : σ ζ = ζ ^ e) (hσt : σ t = ζ ^ c * t)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : ¬(i = 0 ∧ j = 0))
    (hns' : (TateCurve.curve q).toAffine.Nonsingular
      (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j)))) :
    (WeierstrassCurve.Affine.Point.some
        (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j))) hns'
      : (TateCurve.curve q).toAffine.Point)
      = TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht ((e * i + c * j) % p) j := by sorry
