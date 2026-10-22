-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_moment_problem_sup_eq_sup_discrete
-- name    : WassersteinLinOpt.Ball.moment_problem_sup_eq_sup_discrete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T20:25:22.130991+00:00
-- url     : https://prove2.me/theorems/dbc2ae79-518d-491c-9d44-8d761a331dbf
-- title:
--   Proposition 1 (sparsity under (12))
-- statement:
--   Let $Z$ be a topological space with its Borel $\sigma$-algebra, $m\in\mathbb N$, $\psi,\varphi_1,\dots,\varphi_m:Z\to\mathbb R$ Borel functions and $v\in\mathbb R^m$. Let $\mathcal F$ be the set of non-negative finite Borel measures $\gamma$ on $Z$ with $\int_Z\varphi_i\,d\gamma=v_i$ for $i=1,\dots,m$ (the feasible region of problem (11)), $\mathrm{ext}(\mathcal F)$ its extreme points, and $\mathcal D_m(Z)$ the non-negative discrete measures on at most $m$ points.
--
--   **Proposition 1 (first sentence).** Suppose that for every $\gamma\in\mathcal F$ at least one of $\int_Z[\psi]_+\,d\gamma$ and $\int_Z[-\psi]_+\,d\gamma$ is finite. If
--
--   $$\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathcal F\Big\}=\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathrm{ext}(\mathcal F)\Big\}\qquad(12)$$
--
--   then
--
--   $$\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathcal F\Big\}=\sup\Big\{\int_Z\psi\,d\gamma:\gamma\in\mathcal F\cap\mathcal D_m(Z)\Big\}.$$
--
--   This is the infinite-dimensional analogue of "an LP with $m$ equality constraints has an optimal basic solution with at most $m$ nonzero entries", quoted by the paper from Pinelis (2016).
--
--   **Formalization Note.** The paper's hypothesis $\int_Z|\varphi_i|\,d\gamma<\infty$ for all $\gamma\in\mathcal F$ holds by construction, because `momentFeasible` requires `Integrable (φ i) γ` (a real constraint value $v_i$ presupposes a finite integral). Integrals of $\psi$ are the extended-real `quasiIntegral` and all suprema are in `EReal`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1121, Proposition 1 (Appendix B), first sentence; quoted from Pinelis 2016, Corollary 5

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral
import Definitions.Def_WassersteinLinOpt_Ball_discreteMeasures
import Definitions.Def_WassersteinLinOpt_Ball_momentFeasible
import Definitions.Def_WassersteinLinOpt_Ball_measureExtremePoints

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Proposition 1, first sentence (Appendix B, p. 1121; Pinelis 2016, Cor. 5). For problem (11)
on a topological space `Z` with Borel `ψ, φ₁, …, φ_m` and `v ∈ ℝ^m`, with feasible region `𝓕`:
if `ψ` is quasi-integrable under every `γ ∈ 𝓕` and condition (12)
`sup{∫ψ dγ : γ ∈ 𝓕} = sup{∫ψ dγ : γ ∈ ext(𝓕)}` holds, then
`sup{∫ψ dγ : γ ∈ 𝓕} = sup{∫ψ dγ : γ ∈ 𝓕 ∩ 𝒟_m(Z)}`. -/
theorem moment_problem_sup_eq_sup_discrete {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {m : ℕ} (ψ : Z → ℝ) (φ : Fin m → Z → ℝ)
    (v : Fin m → ℝ) (hψ : Measurable ψ) (hφ : ∀ i, Measurable (φ i))
    (hquasi : ∀ γ ∈ momentFeasible φ v,
      ∫⁻ z, ENNReal.ofReal (ψ z) ∂γ < ⊤ ∨ ∫⁻ z, ENNReal.ofReal (-ψ z) ∂γ < ⊤)
    (h12 : (⨆ γ ∈ momentFeasible φ v, quasiIntegral ψ γ) =
      ⨆ γ ∈ measureExtremePoints (momentFeasible φ v), quasiIntegral ψ γ) :
    (⨆ γ ∈ momentFeasible φ v, quasiIntegral ψ γ) =
      ⨆ γ ∈ momentFeasible φ v ∩ discreteMeasures m, quasiIntegral ψ γ := by sorry

end WassersteinLinOpt.Ball
