-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_2_1
-- name    : StochMatchQuery.Union.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:06.088189+00:00
-- url     : https://prove2.me/theorems/4d158f26-4f4c-4928-b5fc-c2010ffdf5c9
-- title:
--   Lemma 2.1 — Sampling properties
-- statement:
--   For a finite simple graph with nonnegative weights, edge probabilities $p_e\in(0,1]$ and a fixed selector, Algorithm 1 with any integer $r\ge0$ satisfies
--   $$q_e\ge\min\{1/3,rx_e/3\}.$$
--   At each vertex, the full family of indicators of incident queried-and-realized edges is negatively associated. This retains the distinction between the query probability and the realized-indicator dependence conclusion.
--
--   Differences from the source: none.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 2.1, PDF/printed p.9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 2 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_2_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w p : Edge G → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w) (r : ℕ) :
    (∀ e, queryProbability G p s r e ≥ min (1/3) ((r : ℝ)*marginal G p s e/3)) ∧
    ∀ v : V, NegativelyAssociated (algorithmLaw G p r)
      (fun e : incident G Finset.univ v => fun z =>
        ind (e.val ∈ queriedRealization G s z.1 z.2)) := by sorry

end
end StochMatchQuery.Union
