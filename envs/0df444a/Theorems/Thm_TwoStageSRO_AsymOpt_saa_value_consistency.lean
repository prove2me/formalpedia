-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_saa_value_consistency
-- name    : TwoStageSRO.AsymOpt.saa_value_consistency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:35.388305+00:00
-- url     : https://prove2.me/theorems/b295ca35-5f76-45b0-8bed-ef5883872b4b
-- title:
--   Proof of Theorem 2, p. 20 — under [A2]–[A3], the SAA optimal value converges a.s. to v*
-- statement:
--   Let $\xi^1,\xi^2,\dots$ be independent random vectors in $\mathbb R^d$ with common law $\mu$, and consider the two-stage stochastic linear problem (OPT) with optimal value $v^*$. Assume
--
--   1. [A2] $v^*$ is finite and $\mathbb E\|\xi\|<\infty$;
--   2. [A3] the set of optimal first-stage decisions of (OPT) is nonempty and bounded.
--
--   Then the optimal value of the sample average approximation converges almost surely:
--   $$\lim_{N\to\infty}\hat v^{SAA}_N=v^*\quad\text{almost surely.}$$
--
--   In the paper this is a cited result (King and Wets 1991, Theorem 3.1; Robinson 1996, Corollary 3.11); it gives the lower half of the main theorem, since $\hat v^{SRO}_N\ge\hat v^{SAA}_N$.
--
--   **Formalization Note** The $\xi^i$ are `ξ 0, ξ 1, …` on a probability space, with `iIndepFun` and `HasLaw (ξ i) μ P`. Values are in `EReal`; "finite" means $\ne\pm\infty$, and $\mathbb E\|\xi\|<\infty$ is `Integrable id μ`. The support condition $P(\xi\in\Xi)=1$ plays no role for (SAA) and is not assumed.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 20, Proof of Theorem 2

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 20, Proof of
Theorem 2 (citing King and Wets 1991, Theorem 3.1, and Robinson 1996, Corollary 3.11): under [A2]–[A3],
`lim_{N→∞} v̂^SAA_N = v*` almost surely.

**Formalization Note** `ξ 0, ξ 1, …` are i.i.d. with law `μ`; the paper's `ξ¹, …, ξᴺ` are
`ξ 0 ω, …, ξ (N-1) ω`. [A2] is `v* ≠ ±∞` and `Integrable id μ`; [A3] is "the optimal set of (OPT) is
nonempty and bounded". The support condition `P(ξ ∈ Ξ) = 1` plays no role in (SAA) and is omitted. -/
theorem saa_value_consistency {n d r m mt : ℕ} (M : Model n d r m mt)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P)
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => vSAA M (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) := by sorry

end TwoStageSRO.AsymOpt
