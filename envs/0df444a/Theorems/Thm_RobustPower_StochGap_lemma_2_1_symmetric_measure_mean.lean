-- Prove2me | Theorems.Thm_RobustPower_StochGap_lemma_2_1_symmetric_measure_mean
-- name    : RobustPower.StochGap.lemma_2_1_symmetric_measure_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:37:23.210453+00:00
-- url     : https://prove2.me/theorems/2da9a127-fb2a-4259-8800-502886ca28b2
-- title:
--   Lemma 2.1 — a symmetric measure has its mean at the point of symmetry
-- statement:
--   Let $S\subseteq\mathbb R^n$ be symmetric with point of symmetry $u^0$, and let $\mu$ be a symmetric probability measure on $S$ (Definition 1.4). If a random vector $x$ drawn from $\mu$ has an expectation, then
--   $$\mathbb E_\mu[x]=u^0 .$$
--
--   Consequently every symmetric probability measure on a symmetric uncertainty set satisfies condition (2.1) of Theorem 2.1 with equality.
--
--   **Formalization Note** Integrability of $x$ is assumed; the page leaves it implicit. It is needed: a symmetric law without a mean (a Cauchy law on $S=\mathbb R$) has no expectation, while Lean's integral of a non-integrable function is $0$, which would make the statement false for $u^0\ne0$. For $S\subseteq\mathbb R^n_+$, as in the paper's applications, $S$ is bounded and integrability is automatic.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 11, Lemma 2.1

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_SymmetricMeasure

open MeasureTheory

namespace RobustPower.StochGap

/-- Lemma 2.1 (p. 11): if `μ` is a symmetric probability measure (Definition 1.4) on the
symmetric set `S ⊆ ℝⁿ` with point of symmetry `u⁰`, and `μ` has a mean, then
`E_μ[x] = u⁰`. -/
theorem lemma_2_1_symmetric_measure_mean {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (S : Set (Fin n → ℝ)) (u₀ : Fin n → ℝ)
    (hμ : IsSymmetricMeasure μ S u₀) (hint : Integrable (fun x : Fin n → ℝ => x) μ) :
    ∫ x, x ∂μ = u₀ := by sorry

end RobustPower.StochGap
