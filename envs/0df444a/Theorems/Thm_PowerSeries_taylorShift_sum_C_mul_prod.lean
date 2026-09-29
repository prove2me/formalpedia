-- Prove2me | Theorems.Thm_PowerSeries_taylorShift_sum_C_mul_prod
-- name    : PowerSeries.taylorShift_sum_C_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/fc99193f-5315-511f-b168-e2c7fd783e90
-- title:
--   Taylor shift of a sum of scaled products of bounded series
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose norm is ultrametric, let $\iota$ be a type, $s$ a finite subset of $\iota$, $c : \iota \to L$ a family of scalars, $\kappa$ a finite type, and $F_{ij} \in L[[T]]$ a doubly indexed family of formal power series over $L$. Let $\rho > 0$ be a real number and assume that for every $i \in s$, every $j \in \kappa$ and every $n$ one has $\|\mathrm{coeff}_n(F_{ij})\|\,\rho^n \le 1$, and let $a \in L$ satisfy $\|a\| < \rho$. For a series $F$ write $F_a$ for the series whose $n$-th coefficient is the sum of the convergent series $\sum_{k \ge 0} \mathrm{coeff}_{n+k}(F)\binom{n+k}{n} a^{k}$, i.e. the formal re-expansion of $F(a+T)$ about $a$. The assertion is the identity of formal power series $$\Bigl(\sum_{i \in s} c_i \prod_{j \in \kappa} F_{ij}\Bigr)_a = \sum_{i \in s} c_i \prod_{j \in \kappa} (F_{ij})_a,$$ where the scalars $c_i$ enter as the constant series $\mathrm{C}(c_i)$ and the products range over all of $\kappa$. No boundedness assumption is imposed on the $c_i$, and the coefficientwise sums defining the shifts are unconditional `tsum`s.
--
--   This is the compatibility of the Taylor shift (re-expansion of a bounded power series at a point of the open disc of radius $\rho$) with finite sums of scalar multiples of finite products, in the setting of Gauss-norm bounds over a complete ultrametric field. It is used in the recentring step for disc charts, where a function given on a chart as a finite combination $\sum_i c_i \prod_j F_{ij}$ of coordinate expansions at the centre must be expanded at an arbitrary point of the disc; the Jensen-type estimate [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le) cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_taylorShift_sum_C_mul_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.taylorShift_sum_C_mul_prod
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    {ι : Type*} (s : Finset ι) (c : ι → L) {κ : Type*} [Fintype κ] (F : ι → κ → PowerSeries L)
    {ρ : ℝ} (hρ : 0 < ρ) (hF : ∀ i ∈ s, ∀ j n, ‖PowerSeries.coeff n (F i j)‖ * ρ ^ n ≤ 1)
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (∑ i ∈ s, PowerSeries.C (c i) * ∏ j, F i j) * ((n + k).choose n : L) * a ^ k)
      = ∑ i ∈ s, PowerSeries.C (c i) * ∏ j, (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F i j) * ((n + k).choose n : L) * a ^ k) := by sorry
