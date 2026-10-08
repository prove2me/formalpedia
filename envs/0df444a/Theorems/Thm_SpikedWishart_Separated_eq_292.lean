-- Prove2me | Theorems.Thm_SpikedWishart_Separated_eq_292
-- name    : SpikedWishart.Separated.eq_292
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:45.085983+00:00
-- url     : https://prove2.me/theorems/b78f059f-3acf-4d06-8fcf-a18b766c3d53
-- title:
--   (292), p. 1690 — e^{−εv}𝓙_∞(v) = (−1)^k i (2π)^{−1/4} √k! e^{−v²/2} p_k(v)
-- statement:
--   Let $k \ge 1$, $\varepsilon, v \in \mathbb R$, and $\mathcal J_\infty(v) = \frac1{2\pi}e^{\varepsilon v}\int_{\Sigma_\infty}s^ke^{\frac12s^2+vs}\,ds$ with $\Sigma_\infty$ the imaginary axis oriented upwards (221). Then
--   $$
--   e^{-\varepsilon v}\mathcal J_\infty(v) = (-1)^k\, i\,(2\pi)^{-1/4}\sqrt{k!}\;e^{-v^2/2}\,p_k(v),
--   $$
--   where $p_k$ is the orthonormal polynomial of (31).
--
--   This expresses the limit of the $\mathcal J$-factor through Hermite polynomials.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1690, (292)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_Separated_Kernels

open Complex

namespace SpikedWishart.Separated

/-- (292), p. 1690: for `k ≥ 1`,
`e^{−εv} 𝓙_∞(v) = (−1)^k i (2π)^{−1/4} √(k!) e^{−v²/2} p_k(v)`. -/
theorem eq_292 (k : ℕ) (hk : 1 ≤ k) (ε v : ℝ) :
    cexp (-((ε * v : ℝ) : ℂ)) * Jinf k ε v =
      (-1) ^ k * I * (((2 * Real.pi) ^ (-(1 / 4 : ℝ)) * Real.sqrt k.factorial *
        Real.exp (-(v ^ 2) / 2) * p k v : ℝ) : ℂ) := by sorry

end SpikedWishart.Separated
