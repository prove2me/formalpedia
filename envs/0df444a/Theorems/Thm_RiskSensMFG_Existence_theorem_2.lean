-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_theorem_2
-- name    : RiskSensMFG.Existence.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:36.003247+00:00
-- url     : https://prove2.me/theorems/735e0713-0260-4c4b-9c4b-82bca51f651d
-- title:
--   Theorem 2, p. 13 — a Markov policy is optimal iff for every $k$ it chooses $\nu^\pi_k$-a.e. a minimizer of $T_kJ_{k+1}(\cdot,\lambda\beta^{k+1})$ (7)
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Fix a measure flow $\mu$, with $p_k$, $c_k$, the infinite-horizon optimal values $J_k(x,\gamma)$ and the operator $T_k$ of §4.1. For a Markov policy $\pi$ let $\nu^\pi_k=\mathcal L(x(k),a(k))$ under $\pi$ and $\mu_0$.
--
--   A Markov policy $\pi$ is optimal, i.e. $J_\mu(\pi)\le J_\mu(\pi')$ for every Markov policy $\pi'$, **if and only if** for every $k\ge0$
--   $$\nu^\pi_k\Big(\Big\{(x,a):\ e^{\lambda\beta^kc_k(x,a)}\int_{\mathsf X}J_{k+1}(y,\lambda\beta^{k+1})\,p_k(dy|x,a)=\big[T_kJ_{k+1}(\cdot,\lambda\beta^{k+1})\big](x)\Big\}\Big)=1.\qquad(7)$$
--
--   The theorem characterizes optimality by an almost-sure pointwise minimization in the dynamic-programming equation. It is what turns the optimality half of the equilibrium condition into the condition $B(\nu)$ on state–action flows in §4.2.
--
--   **Formalization Note** “Policy” and “optimal” are those of §4.1: Markov policies, optimality among Markov policies, for the initial law $\mu_0$ and the cost $J_\mu$ (the proof concludes with $J_0(\pi,x,\lambda)\le J_0(x,\lambda)$ $\mu_0$-a.e.). The set in (7) is kept exactly as printed and measured by $\nu^\pi_k$; under Assumption 1 it is closed, since $J_{k+1}(\cdot,\lambda\beta^{k+1})$ is continuous (Lemma 3). The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all). The flow $\mu$ ranges over all of $\mathcal P(\mathsf X)^\infty$; the paper fixes $\mu\in\mathcal M$ (flows with $\mu_0$ prescribed), but the value at time $0$ of the flow enters only as a parameter of $p$ and $c$, so this is a harmless generalization.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 13, Theorem 2, display (7); proof pp. 13–14

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Theorem 2 (p. 13): a Markov policy `π` is optimal (among Markov policies, for the flow `μ` and
the initial law `μ₀`) if and only if, for every `k`, `ν^π_k`-almost every `(x, a)` attains the
infimum in `[T_k J_{k+1}(·, λβ^{k+1})](x)` (7). -/
theorem theorem_2 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (μ : ℕ → PM X) (π : MarkovPolicy X A) :
    (∀ π' : MarkovPolicy X A, J M μ π.toPolicy ≤ J M μ π'.toPolicy) ↔
      ∀ k : ℕ, stateActionLaw M μ π k
        {xa : X × A | Real.exp (M.lam * M.β ^ k * M.c (xa.1, xa.2, μ k)) *
            ∫ y, JinfOpt M μ (k + 1) y (M.lam * M.β ^ (k + 1)) ∂(M.p (xa.1, xa.2, μ k)) =
          T M μ k (fun y => JinfOpt M μ (k + 1) y (M.lam * M.β ^ (k + 1))) xa.1} = 1 := by sorry

end RiskSensMFG.Existence
