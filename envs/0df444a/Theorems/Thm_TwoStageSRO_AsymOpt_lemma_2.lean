-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_lemma_2
-- name    : TwoStageSRO.AsymOpt.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:52.572578+00:00
-- url     : https://prove2.me/theorems/3edd1755-d0b9-4aac-8a6a-7ba1f6057293
-- title:
--   Lemma 2, p. 16 — Q^C_ϵ̄(x,·) < ∞ on Ξ* gives Q^C_ϵ(λx* + (1 − λ)x, ·) < ∞ on Ξ* for some ϵ > 0
-- statement:
--   Under [A2]–[A3], fix an optimal first-stage decision $x^*$ and let $\Xi^*=\{\zeta\in\Xi:\exists y,\ Tx^*+Wy\ge h(\zeta)\}$. Let $x\in\mathbb R^n$, $\mathcal C\subseteq\mathbb R^{r\times d}$ and $\bar\epsilon>0$ satisfy $Q^{\mathcal C}_{\bar\epsilon}(x,\zeta)<\infty$ for all $\zeta\in\Xi^*$. Then for every $\lambda\in(0,1)$ there exists $\epsilon>0$ such that
--   $$Q^{\mathcal C}_\epsilon\big(\lambda x^*+(1-\lambda)x,\ \zeta\big)<\infty\qquad\text{for all }\zeta\in\Xi^*.$$
--
--   Feasibility of linear decision rules with matrices from $\mathcal C$ is thus transported to first-stage decisions arbitrarily close to $x^*$, at the price of a smaller radius; this is how the proof of the main theorem obtains a feasible point for (MP) near an optimal decision of (OPT).
--
--   **Formalization Note** The conclusion is stated as printed, for $\lambda x^*+(1-\lambda)x$. The law is supported on $\Xi$; [A2]–[A3] and optimality of $x^*$ are the standing assumptions of §4.2. $Q^{\mathcal C}_\epsilon<\infty$ means that some $(y^0,Y)$ with $Y\in\mathcal C$ is feasible on $B(\zeta,\epsilon)\cap\Xi$.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 16, Lemma 2

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 16, Lemma 2:
let `x ∈ ℝⁿ`, `C ⊆ ℝ^{r×d}` and `ε̄ > 0` satisfy `Q^C_ε̄(x, ζ) < ∞` for all `ζ ∈ Ξ*`; then for every
`λ ∈ (0, 1)` there is `ε > 0` with `Q^C_ε(λx* + (1 − λ)x, ζ) < ∞` for all `ζ ∈ Ξ*`.

**Formalization Note** Stated, as printed, for the combination `λx* + (1 − λ)x`. `x*` is `xs`,
optimal for (OPT) under §4.2's standing [A2]–[A3], and `Ξ* = XiStar M xs`. -/
theorem lemma_2 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsupp : μ (Xi M)ᶜ = 0)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (xs : Fin n → ℝ) (hxs : xs ∈ optSet M μ)
    (x : Fin n → ℝ) (C : Set (Matrix (Fin r) (Fin d) ℝ)) (εbar : ℝ) (hεbar : 0 < εbar)
    (hfeas : ∀ ζ ∈ XiStar M xs, QC M p C εbar x ζ < ⊤) :
    ∀ lam ∈ Set.Ioo (0 : ℝ) 1, ∃ ε : ℝ, 0 < ε ∧
      ∀ ζ ∈ XiStar M xs, QC M p C ε (lam • xs + (1 - lam) • x) ζ < ⊤ := by sorry

end TwoStageSRO.AsymOpt
