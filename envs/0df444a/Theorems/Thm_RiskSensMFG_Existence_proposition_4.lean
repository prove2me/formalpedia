-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_proposition_4
-- name    : RiskSensMFG.Existence.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:57.582978+00:00
-- url     : https://prove2.me/theorems/2fd4f090-5541-4945-a423-f1b5d83d73a9
-- title:
--   Proposition 4, p. 16 — the graph of $\Gamma$ is closed in $\Xi\times\Xi$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$. Let $(\alpha,w)$ satisfy (d) and (e) of Assumption 1, and let $\Xi$ and $\Gamma$ be as in §4.2, with $\Xi$ carrying the subspace topology of the product of the weak topologies.
--
--   The graph
--   $$\mathrm{Gr}(\Gamma)=\{(\nu,\xi)\in\Xi\times\Xi:\ \xi\in\Gamma(\nu)\}$$
--   is closed in $\Xi\times\Xi$.
--
--   Together with compactness and convexity of $\Xi$ and nonempty convex values of $\Gamma$, this is the hypothesis of the Kakutani–Fan–Glicksberg fixed-point theorem used to produce a fixed point of $\Gamma$, hence (Proposition 3) a mean-field equilibrium.
--
--   **Formalization Note** Closedness is in $\Xi\times\Xi$ (as printed), not in the ambient product space. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all).
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 16, Proposition 4; proof pp. 16–18

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP
import Definitions.Def_RiskSensMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Proposition 4 (p. 16): the graph `Gr(Γ) = {(ν, ξ) ∈ Ξ × Ξ : ξ ∈ Γ(ν)}` is closed in `Ξ × Ξ`
(`Ξ` with the subspace topology of the product of weak topologies). -/
theorem proposition_4 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M)
    (α : ℝ) (w : X → ℝ) (hw : MomentCondition M α w) :
    IsClosed {q : Xi M α w × Xi M α w | (q.2 : ℕ → PM (X × A)) ∈ Gamma M q.1} := by sorry

end RiskSensMFG.Existence
