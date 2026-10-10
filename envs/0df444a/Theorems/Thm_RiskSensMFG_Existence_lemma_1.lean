-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_lemma_1
-- name    : RiskSensMFG.Existence.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:17.901761+00:00
-- url     : https://prove2.me/theorems/f2c794fb-c29a-4e37-8a77-f4dd5206c433
-- title:
--   Lemma 1, p. 11 — $J^n_k(\cdot,\lambda\beta^k)\in C_b(\mathsf X)$ with $\|J^n_k(\cdot,\lambda\beta^k)\|\le e^{\lambda K\sum_{t=k}^n\beta^t}$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Fix a measure flow $\mu$ and use the notation $J^n_k(x,\gamma)$ of §4.1 for the finite-horizon optimal value over Markov policies.
--
--   For all $n\ge k\ge0$, the function $x\mapsto J^n_k(x,\lambda\beta^k)$ is continuous and bounded, with
--   $$\sup_{x\in\mathsf X}\big|J^n_k(x,\lambda\beta^k)\big|\le e^{\lambda K\zeta_{k,n}},\qquad \zeta_{k,n}=\sum_{t=k}^{n}\beta^t .$$
--
--   The lemma is the base of the dynamic-programming analysis: it shows that the finite-horizon recursion stays in $C_b(\mathsf X)$, where the operator $T_k$ acts.
--
--   **Formalization Note** The page prints $\zeta_{k,n}:=\sum_{t=k}^n\beta^k$, “which is less than $\frac1{1-\beta}$”; that sum equals $(n-k+1)\beta^k$, which is not less than $1/(1-\beta)$ in general. The proof bounds $\lambda\beta^k\sum_{t=k}^n\beta^{t-k}c_t\le\lambda K\sum_{t=k}^n\beta^t$, so the intended quantity is $\sum_{t=k}^n\beta^t<1/(1-\beta)$, which is what is stated (it gives a sharper bound than the printed one). As the paper says on p. 11, in §4.1 *policy* means **Markov policy**: $J^n_k(x,\gamma)$ and $J_k(x,\gamma)$ are infima over Markov policies $\pi=(\pi_t)$, and $J^n_k(\pi,x,\gamma)$, $J_k(\pi,x,\gamma)$ are expectations for the chain started at time $k$ in state $x$ (built by Ionescu–Tulcea from $\delta_x\otimes\pi_k(\cdot|x)$), not conditional expectations of the time-0 chain. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all). The flow $\mu$ ranges over all of $\mathcal P(\mathsf X)^\infty$; the paper fixes $\mu\in\mathcal M$ (flows with $\mu_0$ prescribed), but the value at time $0$ of the flow enters only as a parameter of $p$ and $c$, so this is a harmless generalization.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 11, Lemma 1 (ζ_{k,n} corrected to Σ_{t=k}^n β^t as in its proof, pp. 11–12)

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP

open MeasureTheory ProbabilityTheory Finset

namespace RiskSensMFG.Existence

/-- Lemma 1 (p. 11): for `n ≥ k ≥ 0`, `J^n_k(·, λβ^k)` is continuous and bounded with
`‖J^n_k(·, λβ^k)‖ ≤ exp(λ K ζ_{k,n})`, `ζ_{k,n} = ∑_{t=k}^n β^t` (the proof's value; the page
prints `∑_{t=k}^n β^k`). -/
theorem lemma_1 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (μ : ℕ → PM X) (k n : ℕ) (hkn : k ≤ n) :
    Continuous (fun x => JfinOpt M μ k n x (M.lam * M.β ^ k)) ∧
      ∀ x, |JfinOpt M μ k n x (M.lam * M.β ^ k)| ≤
        Real.exp (M.lam * M.K * ∑ t ∈ Icc k n, M.β ^ t) := by sorry

end RiskSensMFG.Existence
