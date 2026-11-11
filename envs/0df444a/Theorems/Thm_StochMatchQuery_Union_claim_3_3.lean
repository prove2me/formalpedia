-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_3
-- name    : StochMatchQuery.Union.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:44.808805+00:00
-- url     : https://prove2.me/theorems/3d47167a-16e0-4fc3-836e-abd4d4d8ad4a
-- title:
--   Claim 3.3 — One toggle
-- statement:
--   If $M$ and $B'$ are any two matchings of a finite simple graph and $c$ is a nonempty component of their symmetric difference, then
--   $$M\triangle E(c)\text{ is a matching}.$$
--   In particular this applies to every cut component in the round. Exchanges that decrease weight or cardinality are included.
--
--   Differences from the source:
--   - generalization: a component obtained from the cut reference matching → a component of the symmetric difference of any two matchings; reason: the cut matching is a matching, so the source is an immediate instance
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.3, PDF/printed p.14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 3; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (M B' : Realization G) (hM : IsMatching G M) (hB : IsMatching G B')
    (c : Realization G) (hc : component G (toggle G M B') c) : IsMatching G (toggle G M c) := by sorry

end
end StochMatchQuery.Union
