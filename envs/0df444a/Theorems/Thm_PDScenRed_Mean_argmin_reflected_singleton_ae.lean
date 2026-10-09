-- Prove2me | Theorems.Thm_PDScenRed_Mean_argmin_reflected_singleton_ae
-- name    : PDScenRed.Mean.argmin_reflected_singleton_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:39.921822+00:00
-- url     : https://prove2.me/theorems/14601f47-dba3-4a0f-9aea-7e402ec87157
-- title:
--   §4.3, proof of Theorem 3, p. 25, third paragraph — at ζ = ξ̄, 2ζ − ξ ∈ 𝒰 and 𝒵*(2ζ − ξ) is a singleton with probability one
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ be a nonempty bounded polytope, and let $\mathcal U = \{\xi : \min_{z\in\mathcal Z} z'\xi < 0\}$. Let $\xi$ be a random vector in $\mathbb R^d$ with law $\mu$ such that
--
--   1. $\mu$ is absolutely continuous with respect to Lebesgue measure and $\mu(\mathbb R^d\setminus\mathcal U)=0$ (Assumption 5a);
--   2. $\xi$ is integrable, with mean $\bar\xi = \mathbb E[\xi]$ (Assumption 5b, first part);
--   3. $\xi$ and $2\bar\xi-\xi$ have the same law (Assumption 5c).
--
--   Then, with probability one,
--
--   $$2\bar\xi - \xi \in \mathcal U \quad\text{and}\quad \mathcal Z^*(2\bar\xi-\xi) = \arg\min_{z\in\mathcal Z} z'(2\bar\xi - \xi) \text{ is a singleton.}$$
--
--   In the proof of Theorem 3 this is what makes the subdifferential of the first term of $\mathbb E[L(\xi,\zeta)]$ at $\zeta=\bar\xi$ a single vector, $-2\,\mathbb E[\mathcal Z^*(2\bar\xi-\xi)]$.
--
--   **Formalization Note** The paper states the singleton property for a general $\zeta$ with $2\zeta-\xi\in\mathcal U$ and uses it at $\zeta=\bar\xi$; this item is the case $\zeta=\bar\xi$, the one the proof uses. "Symmetric about its mean" is the published `SmartPTO.Fisher.CentrallySymmetric`: the image of $\mu$ under $\xi\mapsto 2\bar\xi-\xi$ is $\mu$.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 25, §4.3, proof of Theorem 3, third paragraph, second sentence; Assumption 5, p. 24

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem argmin_reflected_singleton_ae {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) (hU : μ ((Uset (polytope P qv))ᶜ) = 0)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ξ) μ)
    (hsym : SmartPTO.Fisher.CentrallySymmetric μ) :
    ∀ᵐ ξ ∂μ, (2 : ℝ) • (∫ x, x ∂μ) - ξ ∈ Uset (polytope P qv) ∧
      ∃ z, SmartPTO.Fisher.Wstar (polytope P qv) ((2 : ℝ) • (∫ x, x ∂μ) - ξ) = {z} := by sorry

end PDScenRed.Mean
