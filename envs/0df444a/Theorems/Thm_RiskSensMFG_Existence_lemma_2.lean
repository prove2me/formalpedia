-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_lemma_2
-- name    : RiskSensMFG.Existence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:17.986881+00:00
-- url     : https://prove2.me/theorems/5f8b9305-7c1c-4c7b-95ee-79f19c282992
-- title:
--   Lemma 2, p. 12 — infinite-horizon dynamic programming equation $[T_kJ_{k+1}(\cdot,\lambda\beta^{k+1})](x)=J_k(x,\lambda\beta^k)$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Fix a measure flow $\mu$, with $p_k(\cdot|x,a)=p(\cdot|x,a,\mu_k)$, $c_k(x,a)=c(x,a,\mu_k)$, the infinite-horizon optimal values $J_k(x,\gamma)$ over Markov policies and the operator
--   $$[T_ku](x)=\inf_{a\in\mathsf A}\Big[e^{\lambda\beta^kc_k(x,a)}\int_{\mathsf X}u(y)\,p_k(dy|x,a)\Big]\qquad(4).$$
--   Then for every $k\ge0$ and every $x\in\mathsf X$,
--   $$\big[T_kJ_{k+1}(\cdot,\lambda\beta^{k+1})\big](x)=J_k(x,\lambda\beta^k).$$
--
--   This is the infinite-horizon analogue of the finite-horizon recursion (5), and the identity on which the characterization of optimal policies (Theorem 2) rests.
--
--   **Formalization Note** The paper gives no proof (“a similar conclusion can be derived for $n=\infty$”). As the paper says on p. 11, in §4.1 *policy* means **Markov policy**: $J^n_k(x,\gamma)$ and $J_k(x,\gamma)$ are infima over Markov policies $\pi=(\pi_t)$, and $J^n_k(\pi,x,\gamma)$, $J_k(\pi,x,\gamma)$ are expectations for the chain started at time $k$ in state $x$ (built by Ionescu–Tulcea from $\delta_x\otimes\pi_k(\cdot|x)$), not conditional expectations of the time-0 chain. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all). The flow $\mu$ ranges over all of $\mathcal P(\mathsf X)^\infty$; the paper fixes $\mu\in\mathcal M$ (flows with $\mu_0$ prescribed), but the value at time $0$ of the flow enters only as a parameter of $p$ and $c$, so this is a harmless generalization.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 12, Lemma 2 (no proof printed)

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Lemma 2 (p. 12): `[T_k J_{k+1}(·, λβ^{k+1})](x) = J_k(x, λβ^k)` for every `k ≥ 0`. -/
theorem lemma_2 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (μ : ℕ → PM X) (k : ℕ) (x : X) :
    T M μ k (fun y => JinfOpt M μ (k + 1) y (M.lam * M.β ^ (k + 1))) x =
      JinfOpt M μ k x (M.lam * M.β ^ k) := by sorry

end RiskSensMFG.Existence
