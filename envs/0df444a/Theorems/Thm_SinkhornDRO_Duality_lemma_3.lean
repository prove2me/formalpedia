-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_3
-- name    : SinkhornDRO.Duality.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:08.655547+00:00
-- url     : https://prove2.me/theorems/354bc7b5-da1e-4b31-9f48-27a67c87bcc4
-- title:
--   Lemma 3 — first-order optimality condition (9) and uniqueness when $\lambda^*>0$
-- statement:
--   Under the standing assumptions and Assumption 1, suppose $\bar\rho>0$, Condition 1 holds, and $\lambda^*>0$ minimizes the dual objective of (Dual) over $\lambda\ge0$. Assume moreover that the dual objective is finite at some $\lambda_1\in(0,\lambda^*)$ and is not $-\infty$ at $\lambda^*$. Then $\lambda^*$ is the unique minimizer, and
--
--   $$
--   \frac1{\lambda^*}\,\mathbb E_{x\sim\widehat{\mathbb P}}\left[\frac{\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda^*c(x,z))/(\lambda^*\epsilon)}f(z)\big]}{\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda^*c(x,z))/(\lambda^*\epsilon)}\big]}\right]-\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda^*c(x,z))/(\lambda^*\epsilon)}\big]\Big]=\rho.\qquad(9)
--   $$
--
--   Equation (9) says that the Sinkhorn distance from $\widehat{\mathbb P}$ to the tilted distribution built from $\lambda^*$ is exactly $\rho$: the ball constraint is binding. Note that the right-hand side is $\rho$, not $\bar\rho$.
--
--   **Formalization Note** (9) is the vanishing of the derivative of the dual objective at $\lambda^*$. Two hypotheses are added: finiteness of the dual objective at some $\lambda_1<\lambda^*$, and $>-\infty$ at $\lambda^*$. Without the first, $\lambda^*$ can be the left end of the domain where the objective is finite, with positive right derivative, and (9) fails: e.g. $\widehat{\mathbb P}=\delta_0$ on $\mathcal Z=\mathbb N$, counting $\nu$, $\epsilon=1$, $c(0,z)=z+3\log(1+z)$, $f(z)=z$ and $\bar\rho$ large give $\lambda^*=1$ with (9) a strict inequality. The two sides of (9) are computed in the extended reals with the extended expectation `DupacovaWets.Consistency.expect`; under the hypotheses every term is finite.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 13, Lemma 3, eq. (9) (proof p. ec17)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma 3 (first-order optimality condition when `λ* > 0`), Wang, Gao, Xie, *Sinkhorn
Distributionally Robust Optimization*, arXiv:2109.11926v5, p. 13. Suppose `ρ̄ > 0`, Condition 1
holds, and `λ* > 0` minimizes the dual objective of (Dual) over `λ ≥ 0`. Then the minimizer is
unique and
`(1/λ*) E_{x∼P̂}[E_ν[e^{(f−λ*c(x,·))/(λ*ε)} f] / E_ν[e^{(f−λ*c(x,·))/(λ*ε)}]]
  − ε E_{x∼P̂}[log E_ν[e^{(f−λ*c(x,·))/(λ*ε)}]] = ρ`   (9).

Added hypotheses (the derivation sets the derivative of the dual objective to zero, which presumes
that the objective is finite on a neighbourhood of `λ*`): the dual objective is finite at some
`λ₁ ∈ (0, λ*)`, and is not `−∞` at `λ*`. -/
theorem lemma_3 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat)
    (hρbar : 0 < rhoBar Phat ν c ε ρ) (hC : Condition1 Phat ν c ε f)
    (lamStar : ℝ) (hpos : 0 < lamStar)
    (hmin : IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) lamStar)
    (hinterior : ∃ lam₁ : ℝ, 0 < lam₁ ∧ lam₁ < lamStar ∧ dualObj Phat ν c ε ρ f lam₁ < ⊤)
    (hbot : ⊥ < dualObj Phat ν c ε ρ f lamStar) :
    (∀ μ ∈ Set.Ici (0 : ℝ), IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) μ → μ = lamStar) ∧
      (let w : Z → Z → ℝ≥0∞ := fun x z =>
          EReal.exp ((((lamStar * ε)⁻¹ : ℝ) : EReal) * f z) * kexp c ε x z
        let D : Z → ℝ≥0∞ := fun x => ∫⁻ z, w x z ∂ν
        let N : Z → EReal := fun x => expect ν (fun z => ((w x z : ℝ≥0∞) : EReal) * f z)
        ((lamStar⁻¹ : ℝ) : EReal) * expect Phat (fun x => N x * (((D x)⁻¹ : ℝ≥0∞) : EReal)) -
            (ε : EReal) * expect Phat (fun x => ENNReal.log (D x)) = (ρ : EReal)) := by sorry

end SinkhornDRO.Duality
