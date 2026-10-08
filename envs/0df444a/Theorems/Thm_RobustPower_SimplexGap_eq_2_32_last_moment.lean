-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_eq_2_32_last_moment
-- name    : RobustPower.SimplexGap.eq_2_32_last_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:29:27.42459+00:00
-- url     : https://prove2.me/theorems/e706cde2-65b1-4d83-bc61-03c6ef948931
-- title:
--   Eq. (2.32), numerator — the integral of xₙ over the corner simplex is 1/(n+1)!
-- statement:
--   Let $n\ge 3$ and $\Delta_n=\{x\in\mathbb R^n: x\ge 0,\ \sum_{j=1}^n x_j\le 1\}$. Then
--   $$\int_{\Delta_n}x_n\,dx=\int_{x_1=0}^{1}\int_{x_2=0}^{1-x_1}\cdots\int_{x_n=0}^{1-(x_1+\dots+x_{n-1})}x_n\,dx_n\,dx_{n-1}\cdots dx_1=\frac{1}{(n+1)!}.$$
--
--   This is the numerator of (2.32) in the proof of Theorem 2.6. Together with $\operatorname{vol}(\Delta_n)=1/n!$ it gives the mean $1/(n+1)$ of a coordinate under the uniform distribution on the simplex.
--
--   **Formalization Note** The integral is the Bochner set integral over $\Delta_n$ with respect to Lebesgue measure on `Fin n → ℝ`; the integrand is bounded on a set of finite measure, so it is integrable and the value is not a junk default. The $n$-th coordinate is index $n-1$ of `Fin n`.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 20, proof of Theorem 2.6, Eq. (2.32) (numerator)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

open MeasureTheory

/-- Eq. (2.32), numerator: the integral of the last coordinate `xₙ` over the corner simplex (2.29)
in `ℝⁿ` is `1/(n+1)!`. -/
theorem eq_2_32_last_moment (n : ℕ) (hn : 3 ≤ n) :
    ∫ x in cornerSimplex n, x ⟨n - 1, by omega⟩ = 1 / ((n + 1).factorial : ℝ) := by sorry

end RobustPower.SimplexGap
