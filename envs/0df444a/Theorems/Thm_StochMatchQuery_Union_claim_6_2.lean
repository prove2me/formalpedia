-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_6_2
-- name    : StochMatchQuery.Union.claim_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:07.39424+00:00
-- url     : https://prove2.me/theorems/01bc904d-9d8f-4d8d-bd3d-88bdd0b6771a
-- title:
--   Claim 6.2 — Small coordinates
-- statement:
--   Let $G$ have nonnegative weights and nonuniform edge probabilities in $(0,1]$, with nonempty edge set. Let $x_e$ be its optimum marginal under a fixed selector, and let $Q,\mathcal Q$ come from Algorithm 1. Assume the complete setting of Lemma 6.1: $h,\beta\in(0,1/10]$, $K\ge1$, $0<b\le b_0(K)$, $x_e/p_e\le b$ on $N$; $(M,A)$ is independent of $(Q,\mathcal G_N)$; $M$ is a matching and $A$ avoids its matched vertices. Vertex and pair availability floors, capacity, the absolute covariance row bound and (6.6) all hold. Write $I_v,\pi_v,\pi_{uv},g_e,L_v,f_e$ for the quantities in §6.
--
--   Every $e\in N$ satisfies
--   $$g_e\le\kappa/2\le h/4.$$
--   This bounds both the rounding coordinates and the contribution of one edge to a vertex load.
--
--   Differences from the source:
--   - encoding: p is the minimum of the edge probabilities → the edge set is nonempty where its minimum is used; reason: the minimum in the source is undefined for an edgeless graph
--   - encoding: r ≥ 6/(κβ²p), where p is the minimum edge probability → 6/(κβ²pₑ) ≤ r for every edge; reason: on a nonempty finite edge set this is equivalent to the minimum-probability bound
--   - encoding: edges with zero optimal marginal are removed before the load construction → zero-marginal edges remain with coefficient zero; reason: real division sends 0/0 to zero; their load, objective, and fractional coordinates are identically zero
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 6.2, PDF/printed p.25. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 6 2; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_6_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p w : Edge G → ℝ)
    (hne : (Finset.univ : Realization G).Nonempty)
    (s : Selector G w) (r : ℕ) (N : Realization G) (actual : Ω → Realization G)
    (samples : Ω → Fin r → Realization G) (M : Ω → Realization G) (A : Ω → Finset V)
    (h beta K b : ℝ)
    (H : NonCrucialData G μ p w s r N actual samples M A h beta K b) : ∀ e ∈ N,
    coefficient G μ p s r A e ≤ kappa h beta/2 ∧ kappa h beta/2 ≤ h/4 := by sorry

end
end StochMatchQuery.Union
