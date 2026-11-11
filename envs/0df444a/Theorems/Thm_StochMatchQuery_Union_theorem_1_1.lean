-- Prove2me | Theorems.Thm_StochMatchQuery_Union_theorem_1_1
-- name    : StochMatchQuery.Union.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:23.737177+00:00
-- url     : https://prove2.me/theorems/1ee7b0ba-e2ca-4388-b592-3a062b3f2736
-- title:
--   Theorem 1.1 — goal
-- statement:
--   Let $\varepsilon\in(0,1)$. There exists $C_\varepsilon>0$, depending only on $\varepsilon$, such that the following holds for every finite undirected simple graph with nonempty edge set, arbitrary nonnegative real edge weights, probabilities $p_e\in(0,1]$, and every fixed deterministic maximum-weight selector. With $p=\min_ep_e$, run Algorithm 1 using $r=\lceil C_\varepsilon/p\rceil$ independent samples, independently of the actual realization. Then
--   $$\Delta(Q)\le r\quad\hbox{in every sample outcome},\qquad\mathbb E[w(\operatorname{MWM}(\mathcal Q))]\ge(1-\varepsilon)\mathbb E[w(\operatorname{MWM}(\mathcal G))].$$
--   This is the full query-degree and approximation guarantee; no restriction on bipartiteness, weight range, or uniformity of probabilities is imposed.
--
--   Differences from the source:
--   - encoding: p is the minimum of the edge probabilities → the edge set is nonempty where its minimum is used; reason: the minimum in the source is undefined for an edgeless graph
--   - reading: a fixed tie-breaking rule in Algorithm 1 → every deterministic maximum-weight selector, shared by all samples and OPT; reason: the source does not specify a particular rule; this reading preserves the strongest uniform claim
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Theorem 1.1, PDF/printed p.2–3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- theorem 1 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem theorem_1_1 (eps : ℝ) (heps : 0 < eps ∧ eps < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (w p : Edge G → ℝ)
      (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 < p e ∧ p e ≤ 1)
      (hne : (Finset.univ : Realization G).Nonempty) (s : Selector G w),
      let r := ⌈C / minProbability G p hne⌉₊
      (∀ samples : Fin r → Realization G, maxDegree G (querySet G s samples) ≤ r) ∧
      algorithmValue G p s r ≥ (1-eps) * expectedOpt G (w := w) p := by sorry

end
end StochMatchQuery.Union
