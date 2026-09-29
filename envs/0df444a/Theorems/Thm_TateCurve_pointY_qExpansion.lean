-- Prove2me | Theorems.Thm_TateCurve_pointY_qExpansion
-- name    : TateCurve.pointY_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ba5bdcc7-dca9-5ae1-8be0-12655d05d0d7
-- title:
--   Divisor-sum q-expansion of the Tate curve Y-coordinate
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q,u \in K$ satisfy: $q \neq 0$ and $\|q\| < 1$; $u \neq 0$ and $q^{n}u \neq 1$ for every $n \in \mathbb{Z}$; and the two further smallness conditions $\|qu\| < 1$ and $\|qu^{-1}\| < 1$. Write $y(w) = w^{2}/(1-w)^{3}$, so that `pointY q u` is by definition the sum of the bi-infinite series $\sum_{n \in \mathbb{Z}} y(q^{n}u)$ together with the correction term `s₁ q`. Then $$\mathrm{pointY}\ q\ u \;=\; \frac{u^{2}}{(1-u)^{3}} \;+\; \sum_{N \ge 0} \Bigl(\textstyle\sum_{d \mid N+1} \bigl(\binom{d}{2}(u^{d}-u^{-d}) - d\,u^{-d} + d\bigr)\Bigr) q^{N+1},$$ the inner sum being over the positive divisors of $N+1$, i.e. the $N+1$-st coefficient `yCoeff u (N+1)`; the outer sum is an unconditional sum over $N \in \mathbb{N}$ in $K$.
--
--   This is the $Y$-coordinate half of the classical $q$-expansion of the Tate parametrisation, in the form $Y(u,q) = u^{2}/(1-u)^{3} + \sum_{N\ge 1}\bigl(\sum_{d\mid N}(\binom{d}{2}(u^{d}-u^{-d}) - d\,u^{-d} + d)\bigr)q^{N}$, with the series identified as a divisor sum rather than a double sum. Together with its $X$-coordinate companion it feeds the computations of chord and tangent slopes at non-toric points on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_pointY_qExpansion.lean

import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_TateCurve_Tails

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.pointY_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointY q u = yfun u + ∑' N : ℕ, yCoeff u (N + 1) * q ^ (N + 1) := by sorry
