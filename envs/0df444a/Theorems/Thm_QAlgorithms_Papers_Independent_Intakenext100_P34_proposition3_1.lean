-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_proposition3_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.proposition3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:05:15.017378+00:00
-- url     : https://prove2.me/theorems/1e21097b-db3b-4da4-a12b-9d66e1485c07
-- title:
--   Degenerate intertwiner identities
-- statement:
--   Let $C$ be a commutative unital ring in which $2$ is invertible, let $\epsilon\in\{1,-1\}$, and fix scalars $z_0^{(\ell)}\in C$ for all $\ell\ge0$. Write $\mathcal W_k$ for the actual quotient defined by (2.1)–(2.5) and (2.21)–(2.24), and $z_0(u)=\sum_{\ell\ge0}z_0^{(\ell)}u^{-\ell}$.
--
--   Fix $i\ge1$ and work in $\mathcal W_{i+1}$. All fractions below are geometric expansions at the formal point $u=\infty$. Put $v=(u-y_i)^{-1}$, $w=(u-y_{i+1})^{-1}$, $h=(2u-y_i-y_{i+1})^{-1}$, $t=t_{s_i}$, and $e=e_i$. Then
--   $$
--   (ew-t-h)(ev+t-h)=-(1-h^2),
--   $$
--   $$
--   (w+t-eh)-v(w+t-eh)v=(tvt+t-eh)-w(eve+\epsilon e-eh)w.
--   $$
--   The first identity uses the denominators $u-y_{i+1}$ and $u-y_i$ appearing in the first computation of the source's proof. The printed statement has $1-y$ in those two places. The second identity is unchanged.
--
--   These identities hold in the presented algebra without admissibility assumptions. Their factor order is part of the assertion.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 12, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Proposition 3.1, PDF pp.12--13: both intertwiner identities, in their written order.
In (3.3) the printed denominators 1-y are corrected to u-y, as required by
its first proof computation on p.13. No admissibility or cancellation of e is used. -/
theorem proposition3_1 (P : DParams C) (i : ℕ) (hi : 1 ≤ i) :
    let j : Adj (i+1) := ⟨i-1, by omega⟩
    let m := dwMap C P (i+1)
    let a := m (dy C (adjacentLeft j))
    let b := m (dy C (adjacentRight j))
    let e := ps (m (de C j))
    let t := ps (m (dt C (trans j)))
    let v := infinityResolvent a
    let w := infinityResolvent b
    let h := halfResolvent (algebraMap C (DW C P (i+1)) (↑P.two⁻¹ : C)) (a+b)
    (e*w-t-h)*(e*v+t-h) = -(1-h^2) ∧
    (w+t-e*h)-v*(w+t-e*h)*v =
      (t*v*t+t-e*h)-w*(e*v*e+ps (algebraMap C (DW C P (i+1)) P.epsilon)*e-e*h)*w := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
