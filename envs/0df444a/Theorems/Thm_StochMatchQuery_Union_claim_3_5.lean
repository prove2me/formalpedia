-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_5
-- name    : StochMatchQuery.Union.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:59.425266+00:00
-- url     : https://prove2.me/theorems/5dbce468-4010-4059-b2c4-f0616c32c976
-- title:
--   Claim 3.5 — Conflict degree
-- statement:
--   For every graph outcome $F$ of maximum degree at most $D$, each candidate conflicts with strictly fewer than $d$ present candidates:
--   $$\#\{z\in\mathcal C: z\ne c,\ V(z)\cap V(c)\ne\varnothing,\ E(z)\subseteq F\}<d.$$
--   This is a deterministic bound over all such outcomes.
--
--   Differences from the source: none.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.5, PDF/printed p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 5; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (h : ℝ) (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (F : Realization G) (hd : maxDegree G F ≤ D) :
    ∀ c ∈ candidates G (pieceLength h),
      ((candidates G (pieceLength h)).filter (fun z => conflicts G c z ∧ z ⊆ F)).card < conflictBound D h := by sorry

end
end StochMatchQuery.Union
