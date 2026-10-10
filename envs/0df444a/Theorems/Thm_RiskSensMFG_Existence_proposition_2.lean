-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_proposition_2
-- name    : RiskSensMFG.Existence.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:25.061593+00:00
-- url     : https://prove2.me/theorems/b962628e-9da9-4f2d-9428-18ff04b67f6d
-- title:
--   Proposition 2, p. 16 — $\Gamma(\nu)\subset\Xi$ for every $\nu\in\Xi$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Let $\alpha\ge0$ and $w$ be a constant and a continuous moment function satisfying (d) and (e) of Assumption 1, and let $\Xi=\prod_t\mathcal P^t_w(\mathsf X\times\mathsf A)$ and $\Gamma=C\cap B$ be as in §4.2.
--
--   For every $\nu\in\Xi$,
--   $$\Gamma(\nu)\subset\Xi .$$
--
--   Thus $\Gamma$ maps $\Xi$ into subsets of $\Xi$, which is needed to apply a fixed-point theorem to $\Gamma$ on $\Xi$.
--
--   **Formalization Note** The paper cites the proof to [38, Proposition 3.7]. The pair $(\alpha,w)$ defining $\Xi$ is an explicit argument with its own hypotheses (d), (e); Assumption 1 is also assumed. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all).
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 16, Proposition 2 (cited to [38, Proposition 3.7])

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP
import Definitions.Def_RiskSensMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Proposition 2 (p. 16, cited to [38, Proposition 3.7]): `Γ(ν) ⊂ Ξ` for every `ν ∈ Ξ`. -/
theorem proposition_2 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (α : ℝ) (w : X → ℝ) (hw : MomentCondition M α w) (ν : ℕ → PM (X × A)) (hν : ν ∈ Xi M α w) :
    Gamma M ν ⊆ Xi M α w := by sorry

end RiskSensMFG.Existence
