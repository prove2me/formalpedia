-- Prove2me | Theorems.Thm_RosserSchoenfeld_stechkin_quartic_positivity
-- name    : RosserSchoenfeld.stechkin_quartic_positivity
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-10-03T17:31:51.559242+00:00
-- url     : https://prove2.me/theorems/cad9cec5-6848-432b-8587-6a08635b25dc
-- title:
--   Stechkin positivity for the Rosser-Schoenfeld quartic
-- statement:
--   Let $\sigma>1$ and $t\in\mathbb R$, and define
--
--   $$\sigma_0=\frac{\sqrt{8\sigma^2-4\sigma+1}+1}{2},\qquad \kappa_0=\frac{2\sigma-1}{2\sigma_0-1}.$$
--
--   Let $(a_0,a_1,a_2,a_3,a_4)=(11.1859355312082048,19.073344004352,11.67618784,4.7568,1)$, where every decimal denotes its exact rational value. Prove that
--
--   $$\sum_{k=0}^{4}a_k\operatorname{Re}\!\left(\kappa_0\frac{\zeta'(\sigma_0+ikt)}{\zeta(\sigma_0+ikt)}-\frac{\zeta'(\sigma+ikt)}{\zeta(\sigma+ikt)}\right)\ge 0.$$
--
--   This is the nonnegativity conclusion of equation (1.10) in Rosser and Schoenfeld (1975), specialized to the quartic from page 250. The coefficients satisfy $\sum_{k=0}^{4}a_k\cos(k\theta)=8(0.9126+\cos\theta)^2(0.2766+\cos\theta)^2$. The statement holds throughout $\sigma>1$ and supplies a positivity input for the zero-free-region argument; it does not assert that zero-free region or an estimate for either Chebyshev function.
-- source:
--   J. Barkley Rosser and Lowell Schoenfeld, Sharper Bounds for the Chebyshev Functions theta(x) and psi(x), Mathematics of Computation 29 (129), January 1975, pp. 243-269, DOI 10.1090/S0025-5718-1975-0457373-7, https://doi.org/10.1090/S0025-5718-1975-0457373-7. Parameters: equations (1.3)-(1.4), p. 245. Nonnegativity conclusion: equation (1.10), p. 246. Quartic and exact coefficients: pp. 249-250, especially p. 250.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

theorem RosserSchoenfeld.stechkin_quartic_positivity (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ ∑ k : Fin 5,
      (![11.1859355312082048, 19.073344004352, 11.67618784, 4.7568, 1] : Fin 5 → ℝ) k *
        (((((2 * sigma - 1) /
              (2 * ((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2) - 1) : ℝ) : ℂ) *
            deriv riemannZeta
              (((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2 : ℝ) +
                (k : ℝ) * t * Complex.I) /
            riemannZeta
              (((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2 : ℝ) +
                (k : ℝ) * t * Complex.I)) -
          deriv riemannZeta (sigma + (k : ℝ) * t * Complex.I) /
            riemannZeta (sigma + (k : ℝ) * t * Complex.I)).re := by sorry
