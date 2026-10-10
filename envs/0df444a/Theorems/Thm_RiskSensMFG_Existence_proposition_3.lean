-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_proposition_3
-- name    : RiskSensMFG.Existence.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:41.732562+00:00
-- url     : https://prove2.me/theorems/115d0f20-d320-4ddc-bc98-cc1d8c04bb26
-- title:
--   Proposition 3, p. 16 — a fixed point of $\Gamma$ disintegrates into a mean-field equilibrium
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Let $(\alpha,w)$ satisfy (d) and (e) of Assumption 1 and let $\Xi$, $\Gamma$ be as in §4.2.
--
--   Suppose $\nu=(\nu_t)_{t\ge0}\in\Xi$ is a fixed point of $\Gamma$, $\nu\in\Gamma(\nu)$, and let $\pi=(\pi_t)_{t\ge0}$ be a Markov policy disintegrating each $\nu_t$:
--   $$\nu_t(dx,da)=\nu_{t,1}(dx)\,\pi_t(da\,|\,x)\qquad\text{for all }t\ge0 .$$
--   Put $\nu_1=(\nu_{t,1})_{t\ge0}$. Then $(\pi,\nu_1)$ is a mean-field equilibrium: $\nu_1=\Lambda(\pi)$, and $\pi$ is optimal for $\nu_1$ among all policies.
--
--   This reduces the existence of a mean-field equilibrium to the existence of a fixed point of $\Gamma$.
--
--   **Formalization Note** The statement applies to every Markov policy that disintegrates $\nu$ (the paper says “construct … by disintegrating”); the existence of such a disintegration is not asserted. Optimality is over all history-dependent policies, which is Definition 3 (the paper's proof obtains Markov optimality from Theorem 2 and uses Proposition 1 implicitly). The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all).
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 16, Proposition 3

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_Equilibrium
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP
import Definitions.Def_RiskSensMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Proposition 3 (p. 16): if `ν ∈ Ξ` is a fixed point of `Γ` and the Markov policy `π`
disintegrates every `ν_t` as `ν_t(dx, da) = ν_{t,1}(dx) π_t(da | x)`, then `(π, ν₁)` is a
mean-field equilibrium, `ν₁ = (ν_{t,1})_{t ≥ 0}`. -/
theorem proposition_3 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (α : ℝ) (w : X → ℝ) (hw : MomentCondition M α w) (ν : ℕ → PM (X × A)) (hν : ν ∈ Xi M α w) (hfix : ν ∈ Gamma M ν)
    (π : MarkovPolicy X A)
    (hπ : ∀ t, ProbabilityMeasure.toMeasure (ν t) =
      ProbabilityMeasure.toMeasure (marg (ν t)) ⊗ₘ π.π t) :
    IsMFE M π (fun t => marg (ν t)) := by sorry

end RiskSensMFG.Existence
