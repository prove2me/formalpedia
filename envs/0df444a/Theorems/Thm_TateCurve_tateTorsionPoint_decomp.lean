-- Prove2me | Theorems.Thm_TateCurve_tateTorsionPoint_decomp
-- name    : TateCurve.tateTorsionPoint_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ad6ae743-6142-5de3-9f59-cfa96c09cb68
-- title:
--   Splitting of the Tate torsion parametrisation into ζ- and t-directions
-- statement:
--   Let $K$ be a nontrivially normed, complete, ultrametric field of characteristic zero which is algebraically closed, and let $q,\zeta,t\in K$ with $q\neq 0$ and $\|q\|<1$. Let $p$ be a prime with $p\ge 5$, let $\zeta$ be a primitive $p$-th root of unity and let $t^{p}=q$. For natural numbers $i,j$ with $i<p$ and $j<p$ the assertion is the identity $$\varphi(i,j)=\varphi(i,0)+\varphi(0,j)$$ in the group of affine points of the Weierstrass curve $\mathrm{curve}\,q=\langle 1,0,0,a_4(q),a_6(q)\rangle$ over $K$, where $\varphi(i,j)$ denotes [`TateCurve.tateTorsionPoint`](def/TateCurve_TorsionParametrization.html#L905) at the index pair $(i,j)$: for $i<p$, $j<p$ and $(i,j)\neq(0,0)$ this is the affine point with coordinates $\mathrm{pointX}\,q\,(\zeta^{i}t^{j})=\sum_{n\in\mathbb{Z}}\mathrm{xTerm}\,q\,(\zeta^{i}t^{j})\,n-2s_1(q)$ and $\mathrm{pointY}\,q\,(\zeta^{i}t^{j})=\sum_{n\in\mathbb{Z}}\mathrm{yTerm}\,q\,(\zeta^{i}t^{j})\,n+s_1(q)$, the nonsingularity of the pair being supplied by `nonsingular_point`, and it is the point at infinity otherwise.
--
--   This is the additivity of the Tate parametrisation $u\mapsto\varphi(u)$ restricted to the $p$-torsion parameters $\zeta^{i}t^{j}$, expressing $\varphi(\zeta^{i}\cdot t^{j})=\varphi(\zeta^{i})+\varphi(t^{j})$ in the two coordinate directions. It is used in the construction of the isomorphism [`TateCurve.tateTorsionEquiv_add`](thm.html#TateCurve.tateTorsionEquiv_add) between $(\mathbb{Z}/p)^{2}$ and the $p$-torsion of the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_tateTorsionPoint_decomp.lean

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in

theorem TateCurve.tateTorsionPoint_decomp
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {i j : ℕ} (hi : i < p) (hj : j < p) :
    TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
      = TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
        + TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j := by sorry
