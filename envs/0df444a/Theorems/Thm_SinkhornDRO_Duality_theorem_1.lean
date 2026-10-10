-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_theorem_1
-- name    : SinkhornDRO.Duality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:18.351119+00:00
-- url     : https://prove2.me/theorems/c07c05a2-f1bf-40a3-9600-609e607d9a79
-- title:
--   Theorem 1 — strong duality for Sinkhorn DRO: feasibility iff $\bar\rho\ge0$, $V=V_D$, finiteness, and when $\lambda^*=0$
-- statement:
--   Let $\mathcal Z$ be a measurable space, $\widehat{\mathbb P}$ a probability measure and $\nu\ne0$ a σ-finite measure on $\mathcal Z$, $c:\mathcal Z\times\mathcal Z\to[0,\infty]$ a transport cost, $\epsilon>0$, $\rho\in\mathbb R$, and $f:\mathcal Z\to\mathbb R\cup\{\infty\}$ a loss. Assume Assumption 1 and that $x\mapsto\log\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]$ is $\widehat{\mathbb P}$-integrable, so that
--
--   $$
--   \bar\rho=\rho+\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\nu}\big[e^{-c(x,z)/\epsilon}\big]\Big]\in\mathbb R.
--   $$
--
--   Let $V=\sup\{\mathbb E_{\mathbb P}[f]:\mathcal W_\epsilon(\widehat{\mathbb P},\mathbb P)\le\rho\}$ be the worst-case expected loss over the Sinkhorn ball and
--
--   $$
--   V_D=\inf_{\lambda\ge0}\Big\{\lambda\bar\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\mathbb Q_{x,\epsilon}}\big[e^{f(z)/(\lambda\epsilon)}\big]\Big]\Big\}
--   $$
--
--   the dual value (objective $\operatorname{ess\,sup}_\nu f$ at $\lambda=0$). Then:
--   1. (Primal) is feasible if and only if $\bar\rho\ge0$.
--   2. Whenever $\bar\rho\ge0$, $V=V_D$.
--   3. Suppose $\bar\rho>0$. If the dual objective is finite at some $\lambda>0$, then $V=V_D<\infty$; otherwise $V=V_D=\infty$.
--   4. Suppose $\bar\rho>0$ and Condition 1 holds, and let $A=\{z:f(z)=\operatorname{ess\,sup}_\nu f\}$. The dual minimizer is $\lambda^*=0$ if and only if $\operatorname{ess\,sup}_\nu f<\infty$ and $\bar\rho\ge\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\big[\log\big(1/\mathbb Q_{x,\epsilon}(A)\big)\big]$.
--
--   The theorem turns the infinite-dimensional worst-case problem over a Sinkhorn ball into a one-dimensional convex minimization over $\lambda\ge0$, and identifies when the ball constraint is binding.
--
--   **Formalization Note** Item 3 corrects the paper. The paper states it with Condition 1 ($\mathbb E_{\mathbb Q_{x,\epsilon}}[e^{f/(\lambda\epsilon)}]<\infty$ for $\widehat{\mathbb P}$-a.e. $x$), but that condition does not make $V_D$ finite. Example: $\mathcal Z=\mathbb N$ with counting $\nu$, $\epsilon=1$, $\widehat{\mathbb P}\{x\}\propto x^{-2}$ ($x\ge1$), $f(z)=z^2$, $c(x,z)=|z-x|(1+e^{z^2})$. Every inner expectation is finite but $\mathbb E_{x\sim\widehat{\mathbb P}}[\log\mathbb E_{\mathbb Q_{x,1}}e^{f/\lambda}]=\infty$ for all $\lambda$, so $V=V_D=\infty$. Item 3 is therefore stated with the integrated form of Condition 1 (a finite dual objective at some $\lambda>0$); its "otherwise" branch contains the paper's case where Condition 1 fails. In item 4, "$\lambda^*=0$" means that $0$ is the unique minimizer of the dual objective over $[0,\infty)$, and $\log(1/\mathbb Q_{x,\epsilon}(A))=+\infty$ when $\mathbb Q_{x,\epsilon}(A)=0$. Added hypotheses: $\nu$ σ-finite and nonzero, $\epsilon>0$, and the integrability that makes $\bar\rho$ real. All values are extended reals, and expectations are the published extended expectation `DupacovaWets.Consistency.expect` ($\infty-\infty=+\infty$).
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 7, Theorem 1 (proof pp. 11–13, ec13–ec18)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_SinkhornDistance
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Theorem 1 (strong duality), Wang, Gao, Xie, *Sinkhorn Distributionally Robust Optimization*,
arXiv:2109.11926v5, p. 7. Let `P̂` be a probability measure and assume Assumption 1. Then
(I) (Primal) is feasible if and only if `ρ̄ ≥ 0`;
(II) whenever `ρ̄ ≥ 0`, `V = V_D`;
(III) if `ρ̄ > 0`: when the dual objective is finite at some `λ > 0` (integrated Condition 1),
`V = V_D < ∞`; otherwise `V = V_D = ∞`;
(IV) if `ρ̄ > 0` and Condition 1 holds, with `A = {z : f(z) = ess sup_ν f}`, the dual minimizer is
`λ* = 0` (`0` is the unique minimizer of the dual objective over `λ ≥ 0`) if and only if
`ess sup_ν f < ∞` and `ρ̄ ≥ ε E_{x∼P̂}[log(1/Q_{x,ε}(A))]`.

Correction of (III): the paper's "If Condition 1 holds and ρ̄ > 0, V = V_D < ∞" fails when the
inner expectations are finite `P̂`-a.e. but `x ↦ log E_{Q_{x,ε}}[e^{f/(λε)}]` has infinite
`P̂`-expectation for every `λ > 0`; there `V = V_D = ∞`. The dichotomy is stated with the integrated
form of Condition 1, which covers the paper's "otherwise" case (Condition 1 fails). -/
theorem theorem_1 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat) :
    -- (I)
    ((∃ P : Measure Z, IsProbabilityMeasure P ∧ sinkhornDist Phat ν c ε Phat P ≤ (ρ : EReal)) ↔
        0 ≤ rhoBar Phat ν c ε ρ) ∧
    -- (II)
    (0 ≤ rhoBar Phat ν c ε ρ → primalValue Phat ν c ε ρ f = dualValue Phat ν c ε ρ f) ∧
    -- (III)
    (0 < rhoBar Phat ν c ε ρ →
      (Condition1Integrated Phat ν c ε f →
          primalValue Phat ν c ε ρ f = dualValue Phat ν c ε ρ f ∧ dualValue Phat ν c ε ρ f < ⊤) ∧
        (¬ Condition1Integrated Phat ν c ε f →
          primalValue Phat ν c ε ρ f = ⊤ ∧ dualValue Phat ν c ε ρ f = ⊤)) ∧
    -- (IV)
    (0 < rhoBar Phat ν c ε ρ → Condition1 Phat ν c ε f →
      ((IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) 0 ∧
          ∀ μ ∈ Set.Ici (0 : ℝ), IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) μ → μ = 0) ↔
        (essSup f ν < ⊤ ∧
          (ε : EReal) * expect Phat (fun x => -ENNReal.log (Qker ν c ε x {z | f z = essSup f ν})) ≤
            (rhoBar Phat ν c ε ρ : EReal)))) := by sorry

end SinkhornDRO.Duality
