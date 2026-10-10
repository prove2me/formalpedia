-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_EC_5
-- name    : SinkhornDRO.Duality.lemma_EC_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:14.677047+00:00
-- url     : https://prove2.me/theorems/f2686661-1058-40f0-8c7f-6d8c58dd1e7f
-- title:
--   Lemma EC.5 — $\lambda^*=0$ iff $\operatorname{ess\,sup}_\nu f<\infty$ and $\bar\rho'\ge0$
-- statement:
--   Under the standing assumptions and Assumption 1, suppose $\bar\rho>0$ and Condition 1 holds. Let $A=\{z: f(z)=\operatorname{ess\,sup}_\nu f\}$ with $\operatorname{ess\,sup}_\nu f=\inf\{t:\nu\{f(z)>t\}=0\}$. Then the dual minimizer is $\lambda^*=0$ if and only if both of the following hold:
--   1. $\operatorname{ess\,sup}_\nu f<\infty$;
--   2. $$\bar\rho'=\bar\rho+\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}[\mathbf 1_A(z)]\Big]\ \ge\ 0.$$
--
--   The case $\lambda^*=0$ is the case where the Sinkhorn-ball constraint is not binding: the ball is large enough to contain a distribution concentrated on the maximizers of $f$.
--
--   **Formalization Note** "The dual minimizer $\lambda^*=0$" is formalized as "$0$ is the unique minimizer of the dual objective over $[0,\infty)$". $\mathbb E_{\mathbb Q_{x,\epsilon}}[\mathbf 1_A]=\mathbb Q_{x,\epsilon}(A)$, and $\log 0=-\infty$, so $\bar\rho'=-\infty$ when $\mathbb Q_{x,\epsilon}(A)=0$ on a set of positive $\widehat{\mathbb P}$-measure.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. ec15, Lemma EC.5

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma EC.5 (necessary and sufficient condition for `λ* = 0`), Wang, Gao, Xie, *Sinkhorn
Distributionally Robust Optimization*, arXiv:2109.11926v5, p. ec15. Suppose `ρ̄ > 0` and
Condition 1 holds. Then the dual minimizer is `λ* = 0` (`0` is the unique minimizer of the dual
objective over `λ ≥ 0`) if and only if
(I) `ess sup_ν f < ∞`, and
(II) `ρ̄' = ρ̄ + ε E_{x∼P̂}[log E_{z∼Q_{x,ε}}[1_A(z)]] ≥ 0`, where `A = {z : f(z) = ess sup_ν f}`. -/
theorem lemma_EC_5 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat)
    (hρbar : 0 < rhoBar Phat ν c ε ρ) (hC : Condition1 Phat ν c ε f) :
    (IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) 0 ∧
        ∀ μ ∈ Set.Ici (0 : ℝ), IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) μ → μ = 0) ↔
      (essSup f ν < ⊤ ∧
        0 ≤ (rhoBar Phat ν c ε ρ : EReal) +
          (ε : EReal) * expect Phat (fun x => ENNReal.log (Qker ν c ε x {z | f z = essSup f ν}))) := by sorry

end SinkhornDRO.Duality
