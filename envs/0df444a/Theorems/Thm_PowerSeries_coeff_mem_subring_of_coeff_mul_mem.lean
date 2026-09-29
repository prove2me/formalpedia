-- Prove2me | Theorems.Thm_PowerSeries_coeff_mem_subring_of_coeff_mul_mem
-- name    : PowerSeries.coeff_mem_subring_of_coeff_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e1a898a3-0eae-54db-bcea-6d4d52200b18
-- title:
--   Dividing by a unit-led power series keeps coefficients in a subring
-- statement:
--   Let $K$ be a commutative ring and $R$ a subring of $K$, and let $P,U$ be formal power series in one variable over $K$; let $m_0,L$ be natural numbers. Assume: the coefficient of $q^n$ in $U$ vanishes for every $n<m_0$; there exists $v\in R$ with $v\cdot[q^{m_0}]U=1$ (so the leading coefficient of $U$ is invertible with inverse in $R$); every coefficient of $U$ lies in $R$; and every coefficient of the product $P\cdot U$ in degree $<L$ lies in $R$. Then for each natural number $n$ with $n+m_0<L$, the coefficient $[q^n]P$ lies in $R$. No hypothesis is imposed on the coefficients of $P$ beyond what follows from these, and nothing is asserted about $[q^n]P$ for $n+m_0\ge L$.
--
--   This is the elementary division step used when a $q$-expansion is divided by a power series with unit leading coefficient: integrality of the coefficients of the product, up to a bounded degree, forces integrality of the coefficients of the quotient in the correspondingly smaller range. It is used in the verification of integrality of coefficients of $q$-expansions of slashed modular forms, in [`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`](thm.html#ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.coeff_mem_subring_of_coeff_mul_mem {K : Type*} [CommRing K] (R : Subring K)
    (P U : PowerSeries K) (m₀ L : ℕ)
    (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
    (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
    (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
    (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
    (n : ℕ) (hn : n + m₀ < L) :
    PowerSeries.coeff n P ∈ R := by sorry
