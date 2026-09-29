-- Prove2me | Theorems.Thm_PowerSeries_norm_coeff_taylorShift_mul_pow_le
-- name    : PowerSeries.norm_coeff_taylorShift_mul_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/293037aa-e312-5f86-890f-0d3b541e5165
-- title:
--   Taylor shift inside the disc preserves the Gauss bound
-- statement:
--   Let $L$ be a nontrivially normed field that is complete and whose distance is ultrametric, and let $F \in L[[T]]$ be a formal power series. Let $\rho, M$ be reals with $\rho > 0$, and assume the Gauss-type bound $\|F_m\|\,\rho^m \le M$ for every $m \in \mathbb{N}$, where $F_m$ denotes the $m$-th coefficient of $F$. Let $a \in L$ with $\|a\| < \rho$, and let $n \in \mathbb{N}$. The conclusion is a conjunction: first, the family $k \mapsto F_{n+k}\binom{n+k}{n}a^k$, indexed by $k \in \mathbb{N}$ and with the binomial coefficient taken as an element of $L$ via the canonical map from $\mathbb{N}$, is summable in $L$; second, the power series $G$ whose $m$-th coefficient is by definition the sum $\sum_{k}' F_{m+k}\binom{m+k}{m}a^{k}$ — that is, the Taylor shift of $F$ at $a$, written here as an explicit `PowerSeries.mk` — satisfies $\|G_n\|\,\rho^n \le M$ at the given index $n$. Thus the shifted series obeys the same bound at the same radius $\rho$, with the same constant $M$.
--
--   This is the standard statement that the Taylor shift (recentring) of a power series bounded at radius $\rho$ at a point of the open disc of radius $\rho$ is again bounded at radius $\rho$ with the same constant, so that recentred series stay in the class where evaluation and the Weierstrass-type estimates apply. It underlies the additivity and multiplicativity of the Taylor shift, [`PowerSeries.taylorShift_add`](thm.html#PowerSeries.taylorShift_add) and [`PowerSeries.taylorShift_mul`](thm.html#PowerSeries.taylorShift_mul), and is used in the construction of charts in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_norm_coeff_taylorShift_mul_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.norm_coeff_taylorShift_mul_pow_le {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) ∧
      ‖PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)‖ * ρ ^ n ≤ M := by sorry
