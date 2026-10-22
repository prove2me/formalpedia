-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_moment_problem_condition12
-- name    : WassersteinLinOpt.Ball.moment_problem_condition12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T20:47:42.895265+00:00
-- url     : https://prove2.me/theorems/ba59cd29-dcb6-4cbd-bd31-d4b953371d0d
-- title:
--   Proposition 1 (condition (12) for probability measures on a Hausdorff space)
-- statement:
--   Let $Z$ be a Hausdorff topological space with its Borel $\sigma$-algebra, $m\in\mathbb N$, $\psi,\varphi_1,\dots,\varphi_m:Z\to\mathbb R$ Borel functions and $v\in\mathbb R^m$. Let $\mathcal F$ be the set of non-negative finite Borel measures $\gamma$ on $Z$ with $\int_Z\varphi_i\,d\gamma=v_i$ for $i=1,\dots,m$, and $\mathrm{ext}(\mathcal F)$ its extreme points.
--
--   **Proposition 1 (second sentence).** Suppose that for every $\gamma\in\mathcal F$ at least one of $\int_Z[\psi]_+\,d\gamma$ and $\int_Z[-\psi]_+\,d\gamma$ is finite. If $\mathcal F\subseteq\mathcal P(Z)$, i.e. every feasible measure is a probability measure, then condition (12) holds:
--
--   $$\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathcal F\Big\}=\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathrm{ext}(\mathcal F)\Big\}.$$
--
--   Together with the first sentence of Proposition 1 it yields sparse optimal solutions for moment problems over probability measures, which Theorem 4 applies with $Z=X\times Y$.
--
--   **Formalization Note.** As in the first sentence, `momentFeasible` builds in integrability of each $\varphi_i$, integrals of $\psi$ are `quasiIntegral`, and suprema are in `EReal`. $\mathcal F\subseteq\mathcal P(Z)$ is the hypothesis that every feasible `γ` is an `IsProbabilityMeasure`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1121, Proposition 1 (Appendix B), second sentence; quoted from Pinelis 2016, Proposition 6(v)

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral
import Definitions.Def_WassersteinLinOpt_Ball_momentFeasible
import Definitions.Def_WassersteinLinOpt_Ball_measureExtremePoints

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Proposition 1, second sentence (Appendix B, p. 1121; Pinelis 2016, Prop. 6(v)). For
problem (11) on a Hausdorff space `Z` with Borel `ψ, φ₁, …, φ_m`, `v ∈ ℝ^m` and feasible region
`𝓕`: if `ψ` is quasi-integrable under every `γ ∈ 𝓕` and `𝓕 ⊆ 𝒫(Z)`, then condition (12)
`sup{∫ψ dγ : γ ∈ 𝓕} = sup{∫ψ dγ : γ ∈ ext(𝓕)}` holds. -/
theorem moment_problem_condition12 {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] {m : ℕ} (ψ : Z → ℝ) (φ : Fin m → Z → ℝ)
    (v : Fin m → ℝ) (hψ : Measurable ψ) (hφ : ∀ i, Measurable (φ i))
    (hquasi : ∀ γ ∈ momentFeasible φ v,
      ∫⁻ z, ENNReal.ofReal (ψ z) ∂γ < ⊤ ∨ ∫⁻ z, ENNReal.ofReal (-ψ z) ∂γ < ⊤)
    (hprob : ∀ γ ∈ momentFeasible φ v, IsProbabilityMeasure γ) :
    (⨆ γ ∈ momentFeasible φ v, quasiIntegral ψ γ) =
      ⨆ γ ∈ measureExtremePoints (momentFeasible φ v), quasiIntegral ψ γ := by sorry

end WassersteinLinOpt.Ball
