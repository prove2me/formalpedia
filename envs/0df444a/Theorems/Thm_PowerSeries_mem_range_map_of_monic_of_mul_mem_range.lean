-- Prove2me | Theorems.Thm_PowerSeries_mem_range_map_of_monic_of_mul_mem_range
-- name    : PowerSeries.mem_range_map_of_monic_of_mul_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/77b18431-9004-5889-81a8-ffc299d3cb96
-- title:
--   Integrality plus a denominator forces descent of power series
-- statement:
--   Let $R$ be a commutative domain that is a principal ideal ring, let $K$ be a field with an $R$-algebra structure making $K$ the fraction field of $R$, and write $\iota =$ `PowerSeries.map (algebraMap R K)` for the coefficientwise ring homomorphism $R[[X]] \to K[[X]]$. Let $g \in K[[X]]$, and let $\Phi$ be a monic polynomial in one variable with coefficients in $R[[X]]$ such that $g$ is a root of the polynomial obtained from $\Phi$ by applying $\iota$ to its coefficients, i.e. $\mathrm{eval}_2(\iota, g, \Phi) = 0$ in $K[[X]]$. Suppose further that there is a power series $h \in R[[X]]$ with $h \neq 0$ such that the product $\iota(h) \cdot g$ lies in the image of $\iota$, that is, $\iota(h)\,g = \iota(u)$ for some $u \in R[[X]]$. Then $g$ itself lies in the image of $\iota$: there is $p \in R[[X]]$ with $\iota(p) = g$. In other words, a power series over $K$ which is integral over $R[[X]]$ and admits a nonzero denominator in $R[[X]]$ has all its coefficients in $R$.
--
--   This is the descent step used to convert bounded denominators for an auxiliary multiple of a $q$-expansion into integrality of the $q$-expansion itself; it rests on the normality of $R[[X]]$ for $R$ a principal ideal domain. It is applied with $R = \mathbb{Z}$ in [`ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`](thm.html#ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant). The hypothesis on $h$ cannot be omitted: $\sqrt{4+X} \in \mathbb{Q}[[X]]$ is integral over $\mathbb{Z}[[X]]$ but has unbounded denominators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.mem_range_map_of_monic_of_mul_mem_range
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range := by sorry
