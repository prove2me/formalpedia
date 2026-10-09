-- Prove2me | Theorems.Thm_PDScenRed_Mean_integral_zsel_reflect
-- name    : PDScenRed.Mean.integral_zsel_reflect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:47.404283+00:00
-- url     : https://prove2.me/theorems/0ffbe627-7fc4-4a6c-a7c9-ac79f43529b8
-- title:
--   §4.3, proof of Theorem 3, p. 25, fourth paragraph — 𝔼[z*(2ξ̄ − ξ)] = 𝔼[z*(ξ)] under symmetry
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ be a nonempty bounded polytope and let $z^*:\mathbb R^d\to\mathbb R^d$ be a measurable selection of minimizers, $z^*(\xi)\in\arg\min_{z\in\mathcal Z} z'\xi$ for every $\xi$. Let $\xi$ be an integrable random vector with law $\mu$ and mean $\bar\xi$, and suppose $\xi$ and $2\bar\xi-\xi$ are equal in distribution (Assumption 5c). Then
--
--   $$\mathbb E\big[z^*(2\bar\xi-\xi)\big] = \mathbb E\big[z^*(\xi)\big].$$
--
--   Combined with the previous step, this makes the two parts $-2\,\mathbb E[\mathcal Z^*(2\bar\xi-\xi)]$ and $2\,\mathbb E[z^*(\xi)]$ of the subdifferential of $\mathbb E[L(\xi,\cdot)]$ at $\bar\xi$ cancel, so that $0\in\partial\,\mathbb E[L(\xi,\bar\xi)]$.
--
--   **Formalization Note** Measurability of $z^*$ is needed for $\mathbb E[z^*(\xi)]$ to be meaningful; since $\mathcal Z$ is bounded, $z^*$ is then bounded and both expectations are genuine (not the Bochner integral's junk value).
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 25, §4.3, proof of Theorem 3, fourth paragraph, first sentence

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem integral_zsel_reflect {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ) (hmeas : Measurable zsel)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ξ) μ)
    (hsym : SmartPTO.Fisher.CentrallySymmetric μ) :
    ∫ ξ, zsel ((2 : ℝ) • (∫ x, x ∂μ) - ξ) ∂μ = ∫ ξ, zsel ξ ∂μ := by sorry

end PDScenRed.Mean
