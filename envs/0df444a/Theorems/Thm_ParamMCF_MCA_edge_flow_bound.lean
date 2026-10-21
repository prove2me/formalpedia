-- Prove2me | Theorems.Thm_ParamMCF_MCA_edge_flow_bound
-- name    : ParamMCF.MCA.edge_flow_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:08.84479+00:00
-- url     : https://prove2.me/theorems/766a7ec7-579b-40f0-a25b-29d8602b792d
-- title:
--   §5.2.1, p. 16 — each edge flow of an optimum is bounded by the maximal total inflow
-- statement:
--   Let every edge have a continuous, strictly increasing marginal cost that is nonpositive on negative flows and nonnegative on positive flows. For balanced demands $b^0,b$ and $0\le\lambda\le\lambda^{\max}$, each minimum cost flow $x(\lambda)$ obeys
--
--   $$|x_e(\lambda)|\le x^{\max}\qquad(e\in E).$$
--
--   This bounds the flow range on which marginal costs need to be compared in Lemma 4.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 16, §5.2.1, paragraph before Lemma 4

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- The edge-flow bound in the paragraph preceding Lemma 4, p. 16. -/
theorem edge_flow_bound {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (directed : Bool) (g : E → ℝ → ℝ)
    (hg : ∀ e, IsContinuousMarginalCost (g e))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (lamMax lam : ℝ) (hlamMax : 0 < lamMax) (hlam : lam ∈ Set.Icc 0 lamMax)
    (x : E → ℝ)
    (hx : IsMinCostFlow G directed g (demand b0 b lam) x) :
    ∀ e, |x e| ≤ xmax b0 b lamMax := by sorry

end ParamMCF.MCA
