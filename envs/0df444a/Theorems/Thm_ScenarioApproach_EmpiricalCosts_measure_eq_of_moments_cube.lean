-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_measure_eq_of_moments_cube
-- name    : ScenarioApproach.EmpiricalCosts.measure_eq_of_moments_cube
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:49:44.001015+00:00
-- url     : https://prove2.me/theorems/8c9ff68e-6163-4e27-9fe7-1e1fac582976
-- title:
--   Moment determinacy of probability measures on the unit cube
-- statement:
--   Let $K\ge 0$ and let $\mu,\nu$ be Borel probability measures on $\mathbb R^K$ that are concentrated on the unit cube, $\mu([0,1]^K)=\nu([0,1]^K)=1$. Suppose that all mixed moments of $\mu$ and $\nu$ agree: for every $M\ge 0$ and every word $a:\{1,\dots,M\}\to\{1,\dots,K\}$ of coordinate indices,
--
--   $$
--   \int_{\mathbb R^K}\prod_{j=1}^{M}x_{a(j)}\,\mu(\mathrm dx)=\int_{\mathbb R^K}\prod_{j=1}^{M}x_{a(j)}\,\nu(\mathrm dx).
--   $$
--
--   Then $\mu=\nu$.
--
--   This is the uniqueness half of the multivariate Hausdorff moment problem: a law with compact support is determined by its moments. In the proof of Theorem 8.4 it identifies the joint law of the risks of the empirical costs from the mixed moments of their gaps, which can be computed by adding further independent scenarios to the sample.
--
--   **Formalization Note** Words $a:\mathrm{Fin}\,M\to\mathrm{Fin}\,K$ with repetitions encode all monomials $\prod_i x_i^{m_i}$; $M=0$ gives the total mass.
-- source:
--   Auxiliary lemma for the proof of M. C. Campi, S. Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, doi:10.1137/1.9781611975444, Chapter 8, Sec. 8.1, p. 90, Theorem 8.4 (stated without proof); A. Carè, S. Garatti, M. C. Campi, Scenario min-max optimization and the risk of empirical costs, SIAM J. Optim. 25(4):2061-2080, 2015, doi:10.1137/130928546. Standard fact (moments determine a distribution with bounded support), cf. P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 30 (The Method of Moments); here proved via the Stone-Weierstrass theorem on [0,1]^K.

import Mathlib
namespace ScenarioApproach.EmpiricalCosts

/-- Moment determinacy on the unit cube: two probability measures on `ℝ^K` that are concentrated
on `[0,1]^K` and have the same mixed moments `∫ ∏ⱼ x_{a(j)}` (for every finite word `a` in the
coordinates) are equal. -/
theorem measure_eq_of_moments_cube {K : ℕ} (μ ν : MeasureTheory.Measure (Fin K → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (hμ : μ (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1)
    (hν : ν (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1)
    (h : ∀ (M : ℕ) (a : Fin M → Fin K),
      ∫ x, ∏ j, x (a j) ∂μ = ∫ x, ∏ j, x (a j) ∂ν) :
    μ = ν := by sorry

end ScenarioApproach.EmpiricalCosts
