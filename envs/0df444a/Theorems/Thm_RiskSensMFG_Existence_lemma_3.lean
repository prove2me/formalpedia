-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_lemma_3
-- name    : RiskSensMFG.Existence.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:24.338546+00:00
-- url     : https://prove2.me/theorems/c0118fac-42b3-456c-9708-446ea633b858
-- title:
--   Lemma 3, p. 12 — $\|J^n_k(\cdot,\lambda\beta^k)-J_k(\cdot,\lambda\beta^k)\|\le L_k\beta^{n+1}$, and $J_k(\cdot,\lambda\beta^k)\in C_b(\mathsf X)$ with norm $\le e^{\lambda K/(1-\beta)}$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Fix a measure flow $\mu$ and use the finite- and infinite-horizon optimal values $J^n_k(x,\gamma)$, $J_k(x,\gamma)$ over Markov policies of §4.1. For $k\ge0$ put
--   $$L_k=\frac{\lambda K}{1-\beta}\,e^{\frac{\lambda\beta^kK}{1-\beta}} .$$
--   Then for every $k\ge0$:
--   1. for every $n\ge k$ and every $x\in\mathsf X$,
--   $$\big|J^n_k(x,\lambda\beta^k)-J_k(x,\lambda\beta^k)\big|\le L_k\,\beta^{n+1};$$
--   2. $x\mapsto J_k(x,\lambda\beta^k)$ is continuous;
--   3. $\sup_{x}\big|J_k(x,\lambda\beta^k)\big|\le e^{\lambda K/(1-\beta)}$.
--
--   Since $\beta<1$, the first item says that the finite-horizon optimal values converge to the infinite-horizon one uniformly on $\mathsf X$; the last two then transfer Lemma 1 to the infinite horizon.
--
--   **Formalization Note** The paper's “$\to0$ as $n\to\infty$” is not a separate conjunct: it follows from item 1 because $0<\beta<1$. The bound is stated for every $n\ge k$ (the range on which $J^n_k$ is defined). As the paper says on p. 11, in §4.1 *policy* means **Markov policy**: $J^n_k(x,\gamma)$ and $J_k(x,\gamma)$ are infima over Markov policies $\pi=(\pi_t)$, and $J^n_k(\pi,x,\gamma)$, $J_k(\pi,x,\gamma)$ are expectations for the chain started at time $k$ in state $x$ (built by Ionescu–Tulcea from $\delta_x\otimes\pi_k(\cdot|x)$), not conditional expectations of the time-0 chain. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all). The flow $\mu$ ranges over all of $\mathcal P(\mathsf X)^\infty$; the paper fixes $\mu\in\mathcal M$ (flows with $\mu_0$ prescribed), but the value at time $0$ of the flow enters only as a parameter of $p$ and $c$, so this is a harmless generalization.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 12, Lemma 3; proof p. 13

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Lemma 3 (p. 12): `‖J^n_k(·, λβ^k) − J_k(·, λβ^k)‖ ≤ L_k β^{n+1}` for `n ≥ k`, with
`L_k = (λK/(1−β)) exp(λβ^k K/(1−β))`; and `J_k(·, λβ^k)` is continuous and bounded with
`‖J_k(·, λβ^k)‖ ≤ exp(λK/(1−β))`. -/
theorem lemma_3 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (μ : ℕ → PM X) (k : ℕ) :
    (∀ n, k ≤ n → ∀ x,
      |JfinOpt M μ k n x (M.lam * M.β ^ k) - JinfOpt M μ k x (M.lam * M.β ^ k)| ≤
        (M.lam * M.K / (1 - M.β)) * Real.exp (M.lam * M.β ^ k * M.K / (1 - M.β)) *
          M.β ^ (n + 1)) ∧
    Continuous (fun x => JinfOpt M μ k x (M.lam * M.β ^ k)) ∧
    ∀ x, |JinfOpt M μ k x (M.lam * M.β ^ k)| ≤ Real.exp (M.lam * M.K / (1 - M.β)) := by sorry

end RiskSensMFG.Existence
