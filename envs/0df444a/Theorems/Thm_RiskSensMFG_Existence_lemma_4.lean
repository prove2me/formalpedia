-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_lemma_4
-- name    : RiskSensMFG.Existence.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:11.426274+00:00
-- url     : https://prove2.me/theorems/72eb4506-0dea-4bd4-9d61-c71c89db955d
-- title:
--   Lemma 4, p. 19 — finite-horizon values $J^{\nu^{(n)}}_{*,t}(\cdot,\lambda\beta^t,m+t)$ converge uniformly on compacts when $\nu^{(n)}\to\nu$ in $\Xi$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Let $(\alpha,w)$ satisfy (d) and (e) of Assumption 1, let $\Xi$ be as in §4.2 with the product of the weak topologies, and let $J^\nu_{*,t}(\cdot,\lambda\beta^t,k)$ be the optimal value at time $t$, with finite horizon $k$, of the nonhomogeneous MDP with costs $c(\cdot,\cdot,\nu_{s,1})$ and kernels $p(\cdot|\cdot,\cdot,\nu_{s,1})$.
--
--   Let $\nu^{(n)},\nu\in\Xi$ with $\nu^{(n)}\to\nu$ as $n\to\infty$. Then for all $t\ge0$, all $m\ge0$ and every compact $K\subset\mathsf X$,
--   $$\lim_{n\to\infty}\sup_{x\in K}\big|J^{\nu^{(n)}}_{*,t}(x,\lambda\beta^t,m+t)-J^{\nu}_{*,t}(x,\lambda\beta^t,m+t)\big|=0 .$$
--
--   This is the finite-horizon step towards Proposition 5 and the closed-graph property of $\Gamma$.
--
--   **Formalization Note** The convergence of $\nu^{(n)}$ to $\nu$ is in the product topology on $\mathcal P(\mathsf X\times\mathsf A)^{\mathbb N}$ (the context of the proof of Proposition 4, p. 16). The limit of suprema is stated as uniform convergence on $K$. Policies and infima are Markov, as in §4.1. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all).
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 19, Lemma 4 (inside the proof of Proposition 5); proof pp. 19–20

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP
import Definitions.Def_RiskSensMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Existence

/-- Lemma 4 (p. 19): if `ν^(n) → ν` in `Ξ` (product of weak topologies), then for all `t, m ≥ 0`
and every compact `K ⊂ X`, `sup_{x ∈ K} |J^{ν(n)}_{*,t}(x, λβ^t, m+t) − J^ν_{*,t}(x, λβ^t, m+t)| → 0`. -/
theorem lemma_4 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (α : ℝ) (w : X → ℝ) (hw : MomentCondition M α w) (ν : ℕ → PM (X × A)) (hν : ν ∈ Xi M α w)
    (νn : ℕ → ℕ → PM (X × A)) (hνn : ∀ n, νn n ∈ Xi M α w) (hlim : Tendsto νn atTop (𝓝 ν))
    (t m : ℕ) (Kc : Set X) (hKc : IsCompact Kc) :
    TendstoUniformlyOn (fun n x => CoptFin M (νn n) t (m + t) x)
      (fun x => CoptFin M ν t (m + t) x) atTop Kc := by sorry

end RiskSensMFG.Existence
