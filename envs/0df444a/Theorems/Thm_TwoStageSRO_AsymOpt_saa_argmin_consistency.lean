-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_saa_argmin_consistency
-- name    : TwoStageSRO.AsymOpt.saa_argmin_consistency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:43.194629+00:00
-- url     : https://prove2.me/theorems/7a02ee85-94f2-4879-bf4b-801b9c5cffb0
-- title:
--   Proof of Theorem 2, p. 22 — under [A2]–[A3], accumulation points of η_N-optimal SAA solutions are a.s. optimal for (OPT)
-- statement:
--   Let $\xi^1,\xi^2,\dots$ be independent with common law $\mu$ and assume [A2] ($v^*$ finite, $\mathbb E\|\xi\|<\infty$) and [A3] (the optimal set of (OPT) is nonempty and bounded). Then, almost surely, the following holds: for every sequence $(\hat x_N)$ in $\mathbb R^n$ and every sequence $\eta_N\to0$ such that
--   $$\hat V^{SAA}_N(\hat x_N)\le\hat v^{SAA}_N+\eta_N\qquad\text{for all large }N,$$
--   every accumulation point of $(\hat x_N)$ is an optimal first-stage decision of (OPT).
--
--   In the paper this is a cited result (King and Wets 1991, Proposition 2.1 and Theorem 3.1), applied to $\hat x_N=\hat x^{MP}_N$; it turns the convergence of optimal values into convergence of optimal decisions.
--
--   **Formalization Note** The statement is about arbitrary near-optimal sequences, all quantified inside one almost-sure event; the multi-policy solutions are one instance. Accumulation points are `MapClusterPt`. Values are in `EReal`.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 22, Proof of Theorem 2

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 22, Proof of
Theorem 2 (citing King and Wets 1991, Proposition 2.1 and Theorem 3.1): under [A2]–[A3], almost surely,
for every sequence `x̂_N` and every sequence `η_N → 0` with `V̂^SAA_N(x̂_N) ≤ v̂^SAA_N + η_N` for all large
`N`, every accumulation point of `(x̂_N)` is an optimal first-stage decision of (OPT).

**Formalization Note** The page applies this to `x̂_N = x̂^MP_N`; the statement is for arbitrary
near-optimal sequences, quantified inside one almost-sure event. `MapClusterPt` is "accumulation
point". [A2] and [A3] are encoded as in `saa_value_consistency`. -/
theorem saa_argmin_consistency {n d r m mt : ℕ} (M : Model n d r m mt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ)) :
    ∀ᵐ ω ∂P, ∀ (xh : ℕ → (Fin n → ℝ)) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) →
      (∀ᶠ N in atTop,
        VSAA M (fun i => ξ i ω) N (xh N) ≤ vSAA M (fun i => ξ i ω) N + ((η N : ℝ) : EReal)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ := by sorry

end TwoStageSRO.AsymOpt
