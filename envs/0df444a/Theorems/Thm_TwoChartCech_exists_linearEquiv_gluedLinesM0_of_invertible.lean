-- Prove2me | Theorems.Thm_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible
-- name    : TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/81a64d25-804a-553b-b51b-80d4ee666517
-- title:
--   Invertible modules over the glued-lines chart ring are node twists
-- statement:
--   Let $k$ be a field, let $s$ be a natural number and let $a, b : \mathrm{Fin}\,s \to k^\times$ be two families of units, each assumed injective as a function. Write $A_0$ for the chart ring `(gluedLinesCover k a b).A0`, namely the $k$-subalgebra of $k[T;T^{-1}] \times k[T;T^{-1}]$ cut out by intersecting `gluedLinesOverlap k a b` — the pairs $(f,g)$ with $f(a_i) = g(b_i)$ for every $i$, evaluation being at the units $a_i$, $b_i$ — with the product `(polyPart k).prod (polyPart k)` of the subalgebras of Laurent polynomials all of whose nonvanishing coefficients lie in nonnegative degrees. Let $P$ be an additive commutative group in the same universe as $k$, equipped with an $A_0$-module structure which is invertible in the sense of `Module.Invertible`. Then there exist units $\mu : \mathrm{Fin}\,s \to k^\times$ and an isomorphism of $A_0$-modules between $P$ and `gluedLinesM0 k a b μ`, the $A_0$-submodule of $k[T;T^{-1}] \times k[T;T^{-1}]$ consisting of those pairs $(f,g)$ with both components supported in nonnegative degrees and satisfying $f(a_i) = \mu_i \, g(b_i)$ for all $i$. The isomorphism is asserted in the form `Nonempty` of the type of $A_0$-linear equivalences.
--
--   This is the chart-level form of the computation of the Picard group of two affine lines glued at $s$ pairs of points: every invertible module over the chart ring is, up to isomorphism, one of the explicit node-twisted modules indexed by $\mu \in (k^\times)^s$. It is obtained from [`CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const`](thm.html#CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const) by transporting along the identification of $A_0$ with the corresponding equaliser subalgebra of $k[X] \times k[X]$, and it feeds the statements [`TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible) and [`TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible), which assemble invertible data on the two-chart cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech LaurentPolynomial

universe u

theorem TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (P : Type u) [AddCommGroup P] [Module (gluedLinesCover k a b).A0 P]
    [Module.Invertible (gluedLinesCover k a b).A0 P] :
    ∃ μ : Fin s → kˣ, Nonempty (P ≃ₗ[(gluedLinesCover k a b).A0] ↥(gluedLinesM0 k a b μ)) := by sorry
