-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_EC_4
-- name    : SinkhornDRO.Duality.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:28.782621+00:00
-- url     : https://prove2.me/theorems/1e7cce7d-22c3-4de4-8ed8-f413d70fabbd
-- title:
--   Lemma EC.4 — existence of a dual minimizer
-- statement:
--   Under the standing assumptions and Assumption 1, suppose $\bar\rho>0$ and Condition 1 holds. Then the dual objective
--
--   $$
--   \lambda\ \mapsto\ \lambda\bar\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}\big[e^{f(z)/(\lambda\epsilon)}\big]\Big]\qquad(\lambda\ge0,\ \text{value }\operatorname{ess\,sup}_\nu f\text{ at }\lambda=0)
--   $$
--
--   attains its minimum over $[0,\infty)$ at some $\lambda^*$, and either $\lambda^*=0$ or $\lambda^*$ satisfies the integrability of Condition 1: $\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}[e^{f(z)/(\lambda^*\epsilon)}]<\infty$ for $\widehat{\mathbb P}$-almost every $x$.
--
--   The existence of $\lambda^*$ is what allows the proof of strong duality to split into the cases $\lambda^*>0$ (Lemma 3) and $\lambda^*=0$ (Lemma EC.5).
--
--   **Formalization Note** "$\lambda^*$ satisfies Condition 1" is read as the integrability condition holding at $\lambda=\lambda^*$ itself.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec14, Lemma EC.4

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma EC.4 (existence of dual minimizer), Wang, Gao, Xie, *Sinkhorn Distributionally Robust
Optimization*, arXiv:2109.11926v5, p. ec14. If `ρ̄ > 0` and Condition 1 holds, the dual objective
of (Dual) attains its minimum over `λ ≥ 0` at some `λ*`, and either `λ* = 0` or `λ*` satisfies the
integrability of Condition 1, `E_{z∼Q_{x,ε}}[e^{f(z)/(λ*ε)}] < ∞` for `P̂`-a.e. `x`. -/
theorem lemma_EC_4 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat)
    (hρbar : 0 < rhoBar Phat ν c ε ρ) (hC : Condition1 Phat ν c ε f) :
    ∃ lamStar ∈ Set.Ici (0 : ℝ), IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) lamStar ∧
      (lamStar = 0 ∨ ∀ᵐ x ∂Phat, dualInner ν c ε f lamStar x < ⊤) := by sorry

end SinkhornDRO.Duality
