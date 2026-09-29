-- Prove2me | Theorems.Thm_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
-- name    : Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/457dbadf-a7f3-52d7-9070-dbe4aee1bb3b
-- title:
--   Unit value of a polynomial at one of deg D+1 residues
-- statement:
--   Let $R$ be a commutative ring and let $S$ be a commutative local ring which is an $R$-algebra (both in the same universe). Let $D \in R[X]$ be a polynomial admitting at least one unit coefficient, i.e. there is an index $i$ with $D.\mathrm{coeff}\ i$ a unit of $R$, and let $x \colon \mathrm{Fin}(\deg_{\mathrm{nat}} D + 1) \to S$ be a family of $\deg_{\mathrm{nat}} D + 1$ elements of $S$ such that, for all indices $i, j$, the membership $x_i - x_j \in \mathfrak{m}_S$ in the maximal ideal of $S$ forces $i = j$; equivalently, the $x_i$ have pairwise distinct images in the residue field of $S$. The conclusion is that there exists an index $i$ for which the value $\mathrm{aeval}\ (x_i)\ D \in S$, obtained by evaluating $D$ at $x_i$ through the structure map $R \to S$, is a unit of $S$.
--
--   This is the elementary pigeonhole statement that a polynomial with a unit coefficient cannot take non-unit values at more than $\deg D$ points of a local ring with pairwise distinct residues. It is used to select a point at which a discriminant-type polynomial is invertible, in the constructions [`AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field`](thm.html#AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field) and [`AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (D : Polynomial R) (hD : ∃ i, IsUnit (D.coeff i))
    (x : Fin (D.natDegree + 1) → S) (hx : ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal S → i = j) :
    ∃ i, IsUnit (Polynomial.aeval (x i) D) := by sorry
