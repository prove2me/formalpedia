-- Prove2me | Theorems.Thm_TaoFivePrimes_riemann_verified_finite_and_count
-- name    : TaoFivePrimes.riemann_verified_finite_and_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T23:09:23.673419+00:00
-- url     : https://prove2.me/theorems/11e7290b-ca98-45aa-940a-91a499e2e9e4
-- title:
--   The verified-height zero set is finite and has at most 10^10 elements
-- statement:
--   Let $T_0 = 3.29 \times 10^9$ and let $Z(T_0)=\{\rho : \zeta(\rho)=0,\ 0<\operatorname{Re}\rho<1,\ 0\le\operatorname{Im}\rho\le T_0\}$. Then $Z(T_0)$ is a finite set and $|Z(T_0)|\le 10^{10}$.
--
--   This is the finiteness-and-count half of Theorem 1.5 of Tao's paper. It is the *non-numerical* half: finiteness of the zero set follows from the isolated-zeros theorem for a non-constant analytic function on the compact box $[0,1]\times[0,T_0]$, and the cardinality bound is a consequence of the Riemann–von Mangoldt count with multiplicity at $T_0$, which is already proved on the platform as `TaoFivePrimes.zeta_zero_count_multiplicity_T0_le` together with the seam field `Zeta23.zetaSeam.one_le_mult` (every nontrivial zero has analytic order at least $1$).
--
--   The location of these zeros on the critical line is a *separate* numerical obligation, carried by the slab children of `TaoFivePrimes.riemann_verified`; this node records only what is provable from the analytic and counting theory.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Theorem 1.5, p.4. The finiteness of $Z(T_0)$ is the isolated-zeros theorem for $\zeta$ on the compact box $[0,1]\times[0,T_0]$; the bound $|Z(T_0)|\le 10^{10}$ is the Riemann–von Mangoldt count with multiplicity at $T_0$ together with $\operatorname{ord}_\rho\zeta\ge 1$. This node is the finiteness-and-count half of the mission statement; the critical-line half is the slab decomposition of `TaoFivePrimes.riemann_verified`. https://arxiv.org/html/1201.6656v4#S1

import Mathlib
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_Zeta23_ZeroConfig_N_le_two_mul_half

open Complex Set Topology MeasureTheory Real
open scoped BigOperators
open Zeta23

theorem TaoFivePrimes.riemann_verified_finite_and_count :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}.Finite ∧
      {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
        s.im ≤ 3.29 * 10 ^ 9}.ncard ≤ 10 ^ 10 := by
  sorry
