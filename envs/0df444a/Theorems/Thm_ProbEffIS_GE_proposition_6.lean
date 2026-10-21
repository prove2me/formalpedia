-- Prove2me | Theorems.Thm_ProbEffIS_GE_proposition_6
-- name    : ProbEffIS.GE.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:48.484644+00:00
-- url     : https://prove2.me/theorems/14b4f82a-136a-4cff-ab7f-3cbbde86075f
-- title:
--   Proposition 6 — asymptotic efficiency implies strong probabilistic efficiency
-- statement:
--   For a family of unbiased estimators $Z_\gamma$ of probabilities $p_\gamma\to0$, asymptotic efficiency implies that one sample-size function $n(\gamma)$, subexponential in $-\log p_\gamma$, makes the sample mean strongly probabilistically efficient:
--
--   $$
--   \forall\varepsilon>0,\qquad\delta_\varepsilon(\hat p_\gamma,p_\gamma)\longrightarrow0.
--   $$
--
--   This connects the older second-moment criterion to the paper’s discrepancy criterion. The sampling laws are probability measures eventually, as suffices for an asymptotic assertion.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 17, Proposition 6

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory

namespace ProbEffIS.GE

/-- Proposition 6, p. 17: asymptotic efficiency implies strong probabilistic efficiency. -/
theorem proposition_6 {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (hQ : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ))
    (Z : ℝ → Ω → ℝ)
    (p : ℝ → ℝ) (hp0 : ∀ γ, 0 ≤ p γ) (hp : Tendsto p atTop (𝓝 0))
    (hunb : ∀ᶠ γ in atTop, ∫ ω, Z γ ω ∂(Q γ) = p γ)
    (hAE : AsymptoticallyEfficient Q Z p) :
    StronglyProbEfficient Q Z p := by sorry

end ProbEffIS.GE
