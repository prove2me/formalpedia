-- Prove2me | Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
-- name    : WeierstrassCurve.hasseInvariant_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/7e5fa4d8-33e8-5e6a-a307-2d7139d1552e
-- title:
--   The Hasse invariant has weight q-1
-- statement:
--   Let $R$ be a commutative ring and $q$ a prime natural number such that $R$ has characteristic $q$. Let $W$ be a Weierstrass curve over $R$, given by its coefficients $a_1,\dots,a_6$, and let $v$ be a change of Weierstrass coordinates over $R$, i.e. data $(u,r,s,t)$ with $u \in R^\times$ and $r,s,t \in R$, acting on Weierstrass curves by $v \bullet W$. Here the Hasse invariant $W.\mathrm{hasseInvariant}\ q$ is defined as the coefficient of $X^{q-1}$ in the $\bigl((q-1)/2\bigr)$-th power of the polynomial underlying the two-torsion cubic $\mathrm{twoTorsionPolynomial}$ of $W$, namely $4X^3 + b_2X^2 + 2b_4X + b_6$, with $q-1$ and $(q-1)/2$ computed as natural-number subtraction and truncated division. The assertion is the identity $$(v \bullet W).\mathrm{hasseInvariant}\ q \;=\; (u^{-1})^{q-1}\, W.\mathrm{hasseInvariant}\ q,$$ where $u^{-1}$ is the inverse unit of $u$ viewed in $R$. In particular the Hasse invariant transforms with weight $q-1$ under changes of Weierstrass coordinates, so its vanishing is invariant; for $q = 2$ both sides are $0$.
--
--   This is the classical statement that the Hasse invariant is a modular form of weight $q-1$ in characteristic $q$: it is multiplied by $u^{-(q-1)}$ under the substitution $(x,y) \mapsto (u^2x+r, u^3y+su^2x+t)$. It is used to show that vanishing of the Hasse invariant, i.e. supersingularity, depends only on the isomorphism class of the curve, and hence to characterise the set of supersingular $j$-invariants in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasseInvariant_variableChange.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve

theorem WeierstrassCurve.hasseInvariant_variableChange {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime]
    [CharP R q] (W : WeierstrassCurve R) (v : VariableChange R) :
    (v • W).hasseInvariant q = ((v.u⁻¹ : Rˣ) : R) ^ (q - 1) * W.hasseInvariant q := by sorry
