-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_pi_star_admissible
-- name    : SmoothAmbEq.Gaussian.pi_star_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:24.14173+00:00
-- url     : https://prove2.me/theorems/fffb5d2f-7d0a-4fba-903b-9d22c2cc459f
-- title:
--   Appendix G, p. 39 — π* of (5.12) is admissible
-- statement:
--   Assume $\alpha>\max\{\alpha^*,1-0.5\sigma_0^{-2}\sigma^2T^{-1}\}$ and let $(m_1,\dots,m_6)$ solve (5.10). Then the strategy
--   $$\pi^*(t,x,\beta)=\frac{e^{-r(T-t)}}{k\sigma^2}\big\{a_1(t,m_2(t),m_3(t))+\zeta(t)m_1(t)\big\}(\beta-r)$$
--   belongs to the admissible class $\Pi$ of Definition 5.1.
--
--   This is the first sentence of the proof of Theorem 5.5 ("Obvious, $\pi^*$ is admissible, by Proposition 5.2"); it guarantees that the equilibrium claim is not about an empty or irrelevant class.
--
--   **Formalization Note** The hypotheses are those of Theorem 5.5, in whose proof the claim is made. Admissibility is relative to the given probability space with Brownian motion $W$.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 39, Appendix G

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Appendix G, p. 39: "Obvious, π* is admissible, by Proposition 5.2." Under the hypotheses
of Theorem 5.5 (`α > max{α*, 1 - 0.5σ₀⁻²σ²T⁻¹}`, `(mᵢ)` a solution of (5.10)), the feedback
strategy `π*` of (5.12) belongs to the admissible class `Π` of Definition 5.1. -/
theorem pi_star_admissible (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    Admissible M P W (piStar M c) := by sorry

end SmoothAmbEq.Gaussian
