-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_eq_29
-- name    : SpikedWishart.FixedDim.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:44.407978+00:00
-- url     : https://prove2.me/theorems/88de0f0e-892c-43da-9235-e5baa37cb0dc
-- title:
--   (29), p. 1649 — G₁ is the standard normal distribution function
-- statement:
--   For one particle the finite-GUE distribution is Gaussian: for every real $x$,
--   $$G_1(x) = \frac1{\sqrt{2\pi}}\int_{-\infty}^x e^{-\frac12\xi_1^2}\,d\xi_1 = \Phi(x),$$
--   the distribution function of the standard normal law $N(0,1)$.
--
--   With Proposition 1.1 this recovers the classical central limit theorem for the sample variance of one complex Gaussian variable.
--
--   **Formalization Note** The page writes the right-hand side as "$\mathit{erf}(x)$"; the displayed integral is the standard normal distribution function $\Phi(x)$, which is what is stated (as the $N(0,1)$ measure of $(-\infty,x]$).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1649, §1.2.2, (29)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE

namespace SpikedWishart.FixedDim

open MeasureTheory ProbabilityTheory Set

theorem eq_29 (x : ℝ) : G 1 x = (gaussianReal 0 1).real (Iic x) := by sorry

end SpikedWishart.FixedDim
