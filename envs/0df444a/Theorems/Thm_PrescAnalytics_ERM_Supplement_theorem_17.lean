-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_Supplement_theorem_17
-- name    : PrescAnalytics.ERM.Supplement.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:02:42.974381+00:00
-- url     : https://prove2.me/theorems/aeb98955-fca8-4761-af50-7f4060893262
-- title:
--   Theorem 17 (companion theorem; not used in the proof of the goal) — summable-rho recursive kernel
-- statement:
--   Let $X\in\mathcal X\subseteq\mathbb R^{d_x}$ and $Y\in\mathcal Y\subseteq\mathbb R^{d_y}$ have joint law $\mu$, let $c(z;y)$ be the cost, and let $\mathcal Z\subseteq\mathbb R^{d_z}$ be the decision set. Assume the source's existence, equicontinuity and regularity Assumptions 3–5, including either bounded $\mathcal Z$ or the full conditional-positive-mass coercivity alternative. Samples have marginal law $\mu$. Assume $C>0$, $0<\delta<1/(2d_x)$ and the naïve kernel with $h_i=Ci^{-\delta}$. Sampling is either iid or stationary with $\sum_{k=1}^{\infty}\rho(k)<\infty$; no polynomial-rate condition is added.
--
--   Let $\widehat{\mathcal Z}_N(x)$ be the complete argmin of the corresponding weighted empirical cost. Almost surely in the entire data path, for $\mu_X$-almost every $x$, it is eventually nonempty and every eventual choice $z_N\in\widehat{\mathcal Z}_N(x)$ satisfies
--   $$C(z_N\mid x)\longrightarrow v^*(x),\qquad \inf_{z\in\mathcal Z^*(x)}\|z_N-z\|\longrightarrow0.$$
--   The two limits give decision performance and convergence to the optimizer set. They retain unbounded feasible sets under the second regularity alternative.
--
--   **Formalization Note** Conditional expectations use the published fixed conditional kernel. Both limiting predicates are imported exactly; empirical attainment is part of the conclusion. Positive covariate dimension is explicit because the printed exponent bound divides by $d_x$.
--
--   Differences from the source:
--   - encoding: Finite-dimensional Euclidean observations and weights (13)–(16) use observations 1 through N. → All carriers retain the Euclidean norm; indices start at 0, recursive bandwidth uses i+1, and d_x is positive. Zero normalizers return zero, singular local matrices use the total inverse.; reason: The source bandwidth bounds require positive dimension. Finite-prefix totalization supplies a value where the printed fractions are undefined; no eventual normalization or invertibility is assumed.
--   - reading: Definition 1 says with probability 1, for almost every covariate, both limits hold for the prescribed optimizer. → The probability order is data-path almost surely then covariate almost everywhere, and both limits cover every eventual selection from the eventually nonempty argmin.; reason: This makes the source selection and probability conventions explicit, using the already published predicates and fixed conditional kernel.
--   - encoding: Mixing coefficients tend to zero, with stated polynomial bounds or summability. → Stationarity is explicit; polynomial bounds quantify a finite positive multiplier eventually, and summability starts at lag 1.; reason: With a positive exponent these bounds imply mixing. The imported coefficients use the same normalizations and domains as Definition 5.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 43, Theorem 17

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Prescription
import Definitions.Def_PrescAnalytics_ERM_Supplement_Mixing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Theorem 17, arXiv:1402.5481v4; both alternatives of Assumption 5 retained. -/
theorem theorem_17
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy dz : ℕ} (hdx : 0 < dx)
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS_meas : ∀ i, Measurable (S i)) (hS_law : ∀ i, P.map (S i) = μ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (Xs : Set (EuclideanSpace ℝ (Fin dx))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hXs : ∀ᵐ p ∂μ, p.1 ∈ Xs) (hYs : ∀ᵐ p ∂μ, p.2 ∈ Ys)
    (h3 : PrescAnalytics.KNN.Assumption3 μ c Z)
    (h4 : PrescAnalytics.KNN.Assumption4 c Z Ys)
    (h5 : PrescAnalytics.KNN.Assumption5 μ c Z Xs Ys)
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (hregime : RecursiveRegime P S) (hbandwidth : δ < 1 / (2 * (dx : ℝ))) :
    OptimalAndConsistent P μ c Z (prescription (.recursive) C δ c Z S) := by sorry

end PrescAnalytics.ERM.Supplement
