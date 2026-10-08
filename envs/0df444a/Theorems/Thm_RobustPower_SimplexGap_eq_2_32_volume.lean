-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_eq_2_32_volume
-- name    : RobustPower.SimplexGap.eq_2_32_volume
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:29:19.989662+00:00
-- url     : https://prove2.me/theorems/da9d4d38-f3a3-4e6b-a7a1-7caceca2af2b
-- title:
--   Eq. (2.32), denominator — the corner simplex in ℝⁿ has volume 1/n!
-- statement:
--   Let $n\ge 3$ and $\Delta_n=\{x\in\mathbb R^n: x\ge 0,\ \sum_{j=1}^n x_j\le 1\}$. Its Lebesgue volume is
--   $$\operatorname{vol}(\Delta_n)=\int_{x_1=0}^{1}\int_{x_2=0}^{1-x_1}\cdots\int_{x_n=0}^{1-(x_1+\dots+x_{n-1})}dx_n\,dx_{n-1}\cdots dx_1=\frac{1}{n!}.$$
--
--   This is the denominator of (2.32) in the proof of Theorem 2.6, the normalizing constant of the uniform measure on the simplex.
--
--   **Formalization Note** The volume is Mathlib's Lebesgue measure `volume` on `Fin n → ℝ`, valued in $[0,\infty]$; the iterated integral of the paper is this measure by Fubini. The hypothesis $n\ge 3$ is the standing hypothesis of Theorem 2.6; the formula holds for every $n$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 20, proof of Theorem 2.6, Eq. (2.32) (denominator)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

open MeasureTheory

/-- Eq. (2.32), denominator: the corner simplex (2.29) in `ℝⁿ` has Lebesgue volume `1/n!`. -/
theorem eq_2_32_volume (n : ℕ) (hn : 3 ≤ n) :
    volume (cornerSimplex n) = ((n.factorial : ENNReal))⁻¹ := by sorry

end RobustPower.SimplexGap
