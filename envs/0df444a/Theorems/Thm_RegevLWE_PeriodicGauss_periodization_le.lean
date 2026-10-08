-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_periodization_le
-- name    : RegevLWE.PeriodicGauss.periodization_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:43.327873+00:00
-- url     : https://prove2.me/theorems/d3d03b3b-3802-4171-8657-e53e7fd460f6
-- title:
--   Pp. 34:15–34:16 — reducing modulo 1 cannot increase the statistical distance
-- statement:
--   Let $\varphi_1, \varphi_2 : \mathbb{R} \to \mathbb{R}$ be Lebesgue integrable, and let $\tilde\varphi_i(r) := \sum_{k \in \mathbb{Z}} \varphi_i(r - k)$ be their periodizations, viewed as functions on $\mathbb{T} = [0,1)$. Then
--   $$\int_0^1 \bigl|\tilde\varphi_1(r) - \tilde\varphi_2(r)\bigr|\,dr \le \int_{\mathbb{R}} |\varphi_1(x) - \varphi_2(x)|\,dx .$$
--   When $\varphi_1, \varphi_2$ are the densities of random variables $X, Y$, the periodizations are the densities of $X \bmod 1$ and $Y \bmod 1$, and the inequality is the instance $\Delta(f(X), f(Y)) \le \Delta(X, Y)$, $f = (\cdot \bmod 1)$, of the fact (p. 34:15) that applying a function cannot increase the statistical distance.
--
--   Applied to $\nu_\alpha, \nu_\beta$ it transfers the normal-variable bound to $\Psi_\alpha, \Psi_\beta$.
--
--   **Formalization Note** Only the "modulo 1" instance used in the proof of Claim 2.2 is stated, not the general data-processing inequality for arbitrary (randomized) $f$. Integrability is assumed (the Gaussians satisfy it); it ensures the series converge absolutely for almost every $r$, so the real `tsum` has its true value almost everywhere. Both sides are lower Lebesgue integrals valued in $[0,\infty]$, with no factor $\tfrac12$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:15 (Δ(f(X), f(Y)) ≤ Δ(X, Y)) and p. 34:16, proof of Claim 2.2, second sentence

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- Pp. 34:15–34:16: applying the function "reduce modulo 1" cannot increase the statistical
distance. For integrable `φ₁, φ₂ : ℝ → ℝ`, the periodizations `r ↦ ∑_{k ∈ ℤ} φᵢ(r - k)` on
`𝕋 = [0, 1)` are at statistical distance at most `Δ(φ₁, φ₂)`. -/
theorem periodization_le (φ₁ φ₂ : ℝ → ℝ) (h₁ : Integrable φ₁) (h₂ : Integrable φ₂) :
    statDistT (fun r => ∑' k : ℤ, φ₁ (r - k)) (fun r => ∑' k : ℤ, φ₂ (r - k)) ≤
      statDist φ₁ φ₂ := by sorry

end RegevLWE.PeriodicGauss
