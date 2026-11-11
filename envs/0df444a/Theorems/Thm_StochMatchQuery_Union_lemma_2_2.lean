-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_2_2
-- name    : StochMatchQuery.Union.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:12:32.97633+00:00
-- url     : https://prove2.me/theorems/f983dca4-8cf7-4e44-b045-fa658086a929
-- title:
--   Lemma 2.2 — Small-coordinate rounding
-- statement:
--   Let $f$ be a fractional matching of a finite simple graph with nonnegative weights, and suppose $0\le f_e\le\kappa$ on every edge. Then its support contains a matching $M$ satisfying
--   $$w(M)\ge(1-\kappa)\sum_ew_ef_e.$$
--   The support and attainment of the matching are explicit; there is no bipartiteness restriction.
--
--   Differences from the source: none.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 2.2, PDF/printed p.10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 2 2; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_2_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w f : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hf : InFM G f) (kap : ℝ) (hk : ∀ e, 0 ≤ f e ∧ f e ≤ kap) :
    ∃ M : Realization G, IsMatching G M ∧
      (∀ e ∈ M, f e ≠ 0) ∧ weightOf w M ≥ (1-kap) * ∑ e, w e * f e := by sorry

end
end StochMatchQuery.Union
