-- Prove2me | Theorems.Thm_TwoChartCech_exists_linearEquiv_gluedLinesM1_of_invertible
-- name    : TwoChartCech.exists_linearEquiv_gluedLinesM1_of_invertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/d443ca4c-213d-5c9c-9600-7feeea5e64ee
-- title:
--   Invertible modules over the glued-lines chart ring A₁
-- statement:
--   Let $k$ be a field, let $s$ be a natural number and let $a, b : \mathrm{Fin}\ s \to k^\times$ be two injective families of units of $k$. Write $B$ for the subalgebra of $k[T;T^{-1}] \times k[T;T^{-1}]$ of pairs $(f,g)$ satisfying the $s$ node conditions $f(a_i) = g(b_i)$ for all $i$, where evaluation at a unit is `levalUnit`, and let $A_1 =$ `(gluedLinesCover k a b).A1` be the subalgebra of those $(f,g) \in B$ whose two components each have all coefficients supported in non-positive degrees, i.e. lie in `invPolyPart k`. Let $P$ be an additive commutative group with an $A_1$-module structure which is invertible in the sense of `Module.Invertible`. The assertion is that there is a family of units $\mu : \mathrm{Fin}\ s \to k^\times$ and an $A_1$-linear isomorphism between $P$ and the $A_1$-submodule `gluedLinesM1 k a b μ 0 0` of $k[T;T^{-1}] \times k[T;T^{-1}]$, namely the submodule of pairs $(f,g)$ with $f(a_i) = \mu_i\, g(b_i)$ for all $i$ and with $f$ and $g$ both in `invPolyPart k` (the conditions $f \cdot T^{0}, g \cdot T^{0} \in$ `invPolyPart k` for the degree parameters $n = m = 0$).
--
--   This identifies the Picard group of the second affine chart of two projective lines glued at $s$ pairs of points: every invertible module over that chart ring is realised by one of the explicit node-twisted submodules, the twist being recorded by a family of units $\mu$. It is the counterpart for the chart $A_1$ of the corresponding statement for $A_0$, obtained by transporting the classification of invertible modules over the equaliser subalgebra of $k[X] \times k[X]$ given by [`CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const`](thm.html#CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const), and it feeds the construction of glued-lines sections data in [`TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible) and [`TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_linearEquiv_gluedLinesM1_of_invertible.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech LaurentPolynomial

universe u

theorem TwoChartCech.exists_linearEquiv_gluedLinesM1_of_invertible
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (P : Type u) [AddCommGroup P] [Module (gluedLinesCover k a b).A1 P]
    [Module.Invertible (gluedLinesCover k a b).A1 P] :
    ∃ μ : Fin s → kˣ, Nonempty (P ≃ₗ[(gluedLinesCover k a b).A1] ↥(gluedLinesM1 k a b μ 0 0)) := by sorry
