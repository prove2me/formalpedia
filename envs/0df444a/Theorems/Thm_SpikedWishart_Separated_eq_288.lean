-- Prove2me | Theorems.Thm_SpikedWishart_Separated_eq_288
-- name    : SpikedWishart.Separated.eq_288
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:53.115209+00:00
-- url     : https://prove2.me/theorems/24db4e73-a4eb-4961-b2a8-032401d5bc38
-- title:
--   (285)/(288), p. 1689 — −ie^{εu}𝓗_∞(u) = Res = (−1)^{k−1}(2π)^{1/4}p_{k−1}(u)/√(k−1)! = (−1)^{k−1}(2π)^{1/4}p_k′(u)/√k!
-- statement:
--   Let $k \ge 1$, $\varepsilon, u \in \mathbb R$, and $\mathcal H_\infty(u) = ie^{-\varepsilon u}\,\mathrm{Res}_{a=0}\big(a^{-k}e^{-\frac12a^2 - ua}\big)$ (221). Then
--   $$
--   -ie^{\varepsilon u}\mathcal H_\infty(u) = \mathrm{Res}_{a=0}\Big(\frac1{a^k}e^{-\frac12a^2-ua}\Big) = \frac{(-1)^{k-1}(2\pi)^{1/4}}{\sqrt{(k-1)!}}\,p_{k-1}(u) = \frac{(-1)^{k-1}(2\pi)^{1/4}}{\sqrt{k!}}\,p_k'(u),
--   $$
--   where $p_n$ are the orthonormal polynomials of (31).
--
--   This expresses the limit of the $\mathcal H$-factor through Hermite polynomials.
--
--   **Formalization Note** The page prints the exponent as $-\frac12a^2 - (u+y)a$ inside the residue; the variable $y$ is not bound there, and the definition (221) has $-\frac12a^2 - ua$, which is used. The residue of $a^{-k}\varphi(a)$ for entire $\varphi$ is encoded as $\varphi^{(k-1)}(0)/(k-1)!$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1689, (285) and (288)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_Separated_Kernels

open Complex

namespace SpikedWishart.Separated

/-- (285) and (288), p. 1689: for `k ≥ 1`,
`−i e^{εu} 𝓗_∞(u) = Res_{a=0}(a^{−k} e^{−a²/2 − ua})
  = (−1)^{k−1}(2π)^{1/4}/√((k−1)!) · p_{k−1}(u) = (−1)^{k−1}(2π)^{1/4}/√(k!) · p_k'(u)`. -/
theorem eq_288 (k : ℕ) (hk : 1 ≤ k) (ε u : ℝ) :
    -I * cexp ((ε * u : ℝ) : ℂ) * Hinf k ε u = resAt0 k u ∧
    resAt0 k u = (((-1) ^ (k - 1) * (2 * Real.pi) ^ (1 / 4 : ℝ) /
        Real.sqrt (k - 1).factorial * p (k - 1) u : ℝ) : ℂ) ∧
    resAt0 k u = (((-1) ^ (k - 1) * (2 * Real.pi) ^ (1 / 4 : ℝ) /
        Real.sqrt k.factorial * deriv (p k) u : ℝ) : ℂ) := by sorry

end SpikedWishart.Separated
