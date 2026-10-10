-- Prove2me | Theorems.Thm_SinkhornDRO_Duality_lemma_1
-- name    : SinkhornDRO.Duality.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:43.550885+00:00
-- url     : https://prove2.me/theorems/f2fe39bf-2e39-4acd-9a07-b645141f98b8
-- title:
--   Lemma 1 — weak duality: $V\le\inf_{\lambda\ge0}\{\lambda\rho+\lambda\epsilon\,\mathbb E\log\mathbb E_\nu[e^{(f-\lambda c)/(\lambda\epsilon)}]\}=V_D$
-- statement:
--   Let $\widehat{\mathbb P}$ be a probability measure and $\nu\neq0$ a σ-finite measure on a measurable space $\mathcal Z$, let $c$ be a cost, $\epsilon>0$, $\rho\in\mathbb R$, and $f:\mathcal Z\to\mathbb R\cup\{\infty\}$ a loss, and assume Assumption 1. Assume that $x\mapsto\log\mathbb E_{z\sim\nu}[e^{-c(x,z)/\epsilon}]$ is $\widehat{\mathbb P}$-integrable, so that $\bar\rho$ of (2) is a real number. Then the primal value $V$ of the Sinkhorn DRO problem satisfies
--
--   $$
--   V\ \le\ \inf_{\lambda\ge0}\Big\{\lambda\rho+\lambda\epsilon\,\mathbb E_{x\sim\widehat{\mathbb P}}\Big[\log\mathbb E_{z\sim\nu}\big[e^{(f(z)-\lambda c(x,z))/(\lambda\epsilon)}\big]\Big]\Big\}\ =\ V_D,
--   $$
--
--   where the objective at $\lambda=0$ is $\operatorname{ess\,sup}_\nu f$ and $V_D$ is the value of (Dual), written with $\bar\rho$ and the kernel $\mathbb Q_{x,\epsilon}$.
--
--   This is the easy half of strong duality: every Lagrange multiplier $\lambda\ge0$ of the Sinkhorn-ball constraint gives an upper bound on the worst-case loss.
--
--   **Formalization Note** The conclusion has two parts: the inequality with the $\nu$-form objective (1), and the identity between the infima of (1) and (Dual). The added hypotheses ($\nu$ σ-finite and nonzero, $\epsilon>0$, the integrability that makes $\bar\rho$ real) are the mission's standing assumptions.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 11, Lemma 1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_SinkhornDistance
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)

namespace SinkhornDRO.Duality

/-- Lemma 1 (weak duality), Wang, Gao, Xie, *Sinkhorn Distributionally Robust Optimization*,
arXiv:2109.11926v5, p. 11. Under Assumption 1,
`V ≤ inf_{λ ≥ 0} {λρ + λε E_{x∼P̂}[log E_{z∼ν}[e^{(f(z) − λc(x,z))/(λε)}]]} = V_D`,
where the `λ = 0` term is `ess sup_ν f` (the convention of p. 6) and `V_D` is the value of (Dual). -/
theorem lemma_1 {Z : Type*} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat) :
    primalValue Phat ν c ε ρ f ≤ ⨅ lam ∈ Set.Ici (0 : ℝ), dualObjNu Phat ν c ε ρ f lam ∧
      ⨅ lam ∈ Set.Ici (0 : ℝ), dualObjNu Phat ν c ε ρ f lam = dualValue Phat ν c ε ρ f := by sorry

end SinkhornDRO.Duality
