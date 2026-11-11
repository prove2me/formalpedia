-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_1
-- name    : StochMatchQuery.Union.claim_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:12.466423+00:00
-- url     : https://prove2.me/theorems/79598ebb-8b75-4b5c-9a19-92a2963e1a0d
-- title:
--   Claim 7.1 — Fractional matching, sampled matchings, degree
-- statement:
--   Let $G$ be a finite simple graph with nonnegative weights and $p_e\in(0,1]$, and fix a deterministic selector. For any nonnegative integer $r$, Algorithm 1 has
--   $$x\in\mathcal F_M,\quad M_1,\ldots,M_r\text{ mutually independent with the law of OPT},\quad\Pr(e\notin Q)=(1-x_e)^r,\quad\Delta(Q)\le r.$$
--   The degree assertion holds for every sample outcome. These identify the marginals used throughout the analysis.
--
--   Differences from the source: none.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.1, PDF/printed p.30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w p : Edge G → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w) (r : ℕ) :
    InFM G (marginal G p s) ∧
    iIndepFun (fun j : Fin r => fun z : Realization G × (Fin r → Realization G) =>
      s.choose (z.2 j)) (algorithmLaw G p r) ∧
    (∀ j : Fin r, Measure.map (fun z : Realization G × (Fin r → Realization G) =>
      s.choose (z.2 j)) (algorithmLaw G p r) = Measure.map s.choose (realizationLaw G p)) ∧
    (∀ e, prob (sampleLaw G p r) (fun samples => e ∉ querySet G s samples) =
      (1-marginal G p s e)^r) ∧
    (∀ samples : Fin r → Realization G, maxDegree G (querySet G s samples) ≤ r) := by sorry

end
end StochMatchQuery.Union
