-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_normal_bound
-- name    : RegevLWE.PeriodicGauss.normal_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:40.688916+00:00
-- url     : https://prove2.me/theorems/c08e34d5-a3cb-4fe2-a43e-d3046a4d6b84
-- title:
--   Proof of Claim 2.2, p. 34:16 — normal variables with standard deviations α/√(2π), β/√(2π) are within statistical distance 9(β/α − 1)
-- statement:
--   Let $0 < \alpha < \beta \le 2\alpha$, and let $\nu_\alpha(x) = \frac1\alpha e^{-\pi(x/\alpha)^2}$ and $\nu_\beta(x) = \frac1\beta e^{-\pi(x/\beta)^2}$ be the densities on $\mathbb{R}$ of normal variables with mean $0$ and standard deviations $\alpha/\sqrt{2\pi}$ and $\beta/\sqrt{2\pi}$. Then
--   $$\Delta(\nu_\alpha, \nu_\beta) = \int_{\mathbb{R}} |\nu_\alpha(x) - \nu_\beta(x)|\,dx \le 9\Bigl(\frac{\beta}{\alpha} - 1\Bigr).$$
--
--   This is the statement the proof of Claim 2.2 establishes on the real line; Claim 2.2 follows by reducing modulo $1$.
--
--   **Formalization Note** $\Delta$ is the lower Lebesgue integral `statDist` (no factor $\tfrac12$), valued in $[0,\infty]$; the bound is compared through `ENNReal.ofReal`.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:16, proof of Claim 2.2, first sentence

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- Proof of Claim 2.2, p. 34:16, first sentence: for `0 < α < β ≤ 2α`, the statistical distance
between the normal densities with standard deviations `α/√(2π)` and `β/√(2π)` is at most
`9 (β/α - 1)`. -/
theorem normal_bound (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β ≤ 2 * α) :
    statDist (nu α) (nu β) ≤ ENNReal.ofReal (9 * (β / α - 1)) := by sorry

end RegevLWE.PeriodicGauss
