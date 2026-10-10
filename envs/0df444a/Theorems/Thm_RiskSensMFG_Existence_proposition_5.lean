-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_proposition_5
-- name    : RiskSensMFG.Existence.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:42.000266+00:00
-- url     : https://prove2.me/theorems/70d873a8-4a41-4ca0-bcbc-5486f61c16ea
-- title:
--   Proposition 5, p. 19 — $J^{\nu^{(n)}}_{*,t}\to J^\nu_{*,t}$ uniformly on compacts and continuously when $\nu^{(n)}\to\nu$ in $\Xi$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Let $(\alpha,w)$ satisfy (d) and (e) of Assumption 1, let $\Xi$ be as in §4.2 with the product of the weak topologies, and let $J^\nu_{*,t}(\cdot,\lambda\beta^t)$ be the infinite-horizon optimal value at time $t$ of the nonhomogeneous MDP driven by the state marginals of $\nu$.
--
--   Let $\nu^{(n)},\nu\in\Xi$ with $\nu^{(n)}\to\nu$. Then for every $t\ge0$:
--   1. for every compact $K\subset\mathsf X$,
--   $$\lim_{n\to\infty}\sup_{x\in K}\big|J^{\nu^{(n)}}_{*,t}(x,\lambda\beta^t)-J^{\nu}_{*,t}(x,\lambda\beta^t)\big|=0;$$
--   2. $J^{\nu^{(n)}}_{*,t}$ converges to $J^\nu_{*,t}$ **continuously**: $J^{\nu^{(n)}}_{*,t}(x_n,\lambda\beta^t)\to J^\nu_{*,t}(x,\lambda\beta^t)$ whenever $x_n\to x$.
--
--   This is the continuity of the optimal value functions in the mean-field term on which the closed-graph property (Proposition 4) rests.
--
--   **Formalization Note** “Converges continuously” is the paper's footnote 1, p. 17. Both conclusions are stated. Policies and infima are Markov, as in §4.1. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all).
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 19, Proposition 5; footnote 1 (p. 17) for continuous convergence; proof pp. 19–20

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP
import Definitions.Def_RiskSensMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Existence

/-- Proposition 5 (p. 19): if `ν^(n) → ν` in `Ξ`, then for every compact `K ⊂ X` and `t ≥ 0`,
`sup_{x ∈ K} |J^{ν(n)}_{*,t}(x, λβ^t) − J^ν_{*,t}(x, λβ^t)| → 0`; therefore `J^{ν(n)}_{*,t}`
converges to `J^ν_{*,t}` continuously. -/
theorem proposition_5 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (α : ℝ) (w : X → ℝ) (hw : MomentCondition M α w) (ν : ℕ → PM (X × A)) (hν : ν ∈ Xi M α w)
    (νn : ℕ → ℕ → PM (X × A)) (hνn : ∀ n, νn n ∈ Xi M α w) (hlim : Tendsto νn atTop (𝓝 ν))
    (t : ℕ) :
    (∀ Kc : Set X, IsCompact Kc →
      TendstoUniformlyOn (fun n x => Copt M (νn n) t x) (fun x => Copt M ν t x) atTop Kc) ∧
    ∀ (xn : ℕ → X) (x : X), Tendsto xn atTop (𝓝 x) →
      Tendsto (fun n => Copt M (νn n) t (xn n)) atTop (𝓝 (Copt M ν t x)) := by sorry

end RiskSensMFG.Existence
