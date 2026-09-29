-- Prove2me | Theorems.Thm_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
-- name    : PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a1003122-84dd-514f-9251-b2661cdd213e
-- title:
--   Divisibility of low coefficients of u(X+d)ⁿ-Xⁿ
-- statement:
--   Let $A$ be a commutative ring which is local and a domain, with maximal ideal $\mathfrak m_A$. Let $n$ be a natural number whose image $n\cdot 1$ in $A$ is a unit, let $d \in \mathfrak m_A$, and let $e \in A$ be non-zero. Let $u, F \in A\llbracket X\rrbracket$ be formal power series satisfying the identity
--   $$e \cdot F \;=\; u\,(X + C\,d)^n \;-\; X^n ,$$
--   where $C\,d$ denotes the constant series $d$ and $e\cdot F$ is the scalar multiple of $F$ by $e$. Then for every index $j$ with $j + 2 \le n$ (that is, $j \le n-2$) the element $d$ divides the $j$-th coefficient of $F$ in $A$. Nothing is assumed about the constant coefficient of $u$, and no invertibility of $e$ is assumed beyond $e \neq 0$; the divisibility is asserted coefficientwise, not as a divisibility of $F$ by $C\,d$ in $A\llbracket X\rrbracket$.
--
--   This is the algebraic core of a residue-disc estimate: read with $X$ a parameter on a residue disc centred at a pole, $d$ the difference of two centres and $F$ the expansion of a perturbation, the conclusion says that modulo $\mathfrak m_A$ the series $F$ is divisible by $X^{n-1}$, so that the reduction has at most a simple pole. It is used in the proof of the disc laws for the model [`ModularCurve.XHDRModelAtP`](def/ModularCurve_XHDRModelAtP.html#L81), in `discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing PowerSeries

theorem PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F := by sorry
