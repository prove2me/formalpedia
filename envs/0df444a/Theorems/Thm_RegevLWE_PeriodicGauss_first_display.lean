-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_first_display
-- name    : RegevLWE.PeriodicGauss.first_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:35.00342+00:00
-- url     : https://prove2.me/theorems/80a2bf49-625e-4417-a316-605b25aaa3b0
-- title:
--   Proof of Claim 2.2, p. 34:16 — first display: triangle split of ∫|e^{−πx²} − (1+ϵ)^{−1}e^{−πx²/(1+ϵ)²}|
-- statement:
--   Let $0 < \epsilon \le 1$. All integrals are over $\mathbb{R}$ with respect to Lebesgue measure. Then
--   $$\int \Bigl|e^{-\pi x^2} - \tfrac{1}{1+\epsilon} e^{-\pi x^2/(1+\epsilon)^2}\Bigr|dx \le \int \bigl|e^{-\pi x^2} - e^{-\pi x^2/(1+\epsilon)^2}\bigr|dx + \int \Bigl|\Bigl(1 - \tfrac{1}{1+\epsilon}\Bigr)e^{-\pi x^2/(1+\epsilon)^2}\Bigr|dx,$$
--   the last integral equals $\epsilon$, and
--   $$\int \bigl|e^{-\pi x^2} - e^{-\pi x^2/(1+\epsilon)^2}\bigr|dx = \int \bigl|e^{-\pi(1 - 1/(1+\epsilon)^2)x^2} - 1\bigr|\,e^{-\pi x^2/(1+\epsilon)^2}dx.$$
--   Together these give the chain of the first display in the proof of Claim 2.2: the statistical distance between the normal densities $\nu_1$ and $\nu_{1+\epsilon}$ is at most $\int |e^{-\pi(1-1/(1+\epsilon)^2)x^2} - 1|e^{-\pi x^2/(1+\epsilon)^2}dx + \epsilon$.
--
--   This reduces the comparison of two normal densities to the integral of a single nonnegative function, which the next two steps bound.
--
--   **Formalization Note** Every integral is a lower Lebesgue integral of a nonnegative function, valued in $[0,\infty]$. The printed chain $A \le B + C = B + \epsilon = D + \epsilon$ is stated as its three component facts $A \le B + C$, $C = \epsilon$ and $B = D$, which together imply it.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:16, proof of Claim 2.2, first display

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- Proof of Claim 2.2, p. 34:16, first display. For `0 < ϵ ≤ 1`, with all integrals over `ℝ`,
`∫ |e^{-πx²} - (1/(1+ϵ)) e^{-πx²/(1+ϵ)²}| ≤ ∫ |e^{-πx²} - e^{-πx²/(1+ϵ)²}| + ∫ |(1 - 1/(1+ϵ)) e^{-πx²/(1+ϵ)²}|`,
the second integral equals `ϵ`, and
`∫ |e^{-πx²} - e^{-πx²/(1+ϵ)²}| = ∫ |e^{-π(1-1/(1+ϵ)²)x²} - 1| e^{-πx²/(1+ϵ)²}`. -/
theorem first_display (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - 1 / (1 + ϵ) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ≤
      (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) +
      (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) = ENNReal.ofReal ϵ ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) =
      ∫⁻ x : ℝ, ENNReal.ofReal
        (|Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1| *
          Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) := by sorry

end RegevLWE.PeriodicGauss
