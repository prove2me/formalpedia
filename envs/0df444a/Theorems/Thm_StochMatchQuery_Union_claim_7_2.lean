-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_2
-- name    : StochMatchQuery.Union.claim_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:32.552349+00:00
-- url     : https://prove2.me/theorems/e9f2d9db-2ca6-4d50-8ad9-f9b196c13a39
-- title:
--   Claim 7.2 — Properties of the thresholds
-- statement:
--   For $\varepsilon\in(0,1)$, the threshold recursion of (7.1), (7.3)–(7.4) satisfies, for every $0\le i<J$,
--   $$0<a_i\le1,\quad K_i\ge1,\quad a_{i+1}\le a_i/2<a_i,\quad a_{i+1}\le b_0(K_i).$$
--   All thresholds and covariance constants depend only on $\varepsilon$: their defining functions have no instance arguments. These are uniform thresholds for all input graphs.
--
--   Differences from the source:
--   - encoding: thresholds depend only on ε → threshold and thresholdK are functions of ε and an index, without graph or instance arguments; reason: clause (iii) holds by their definitions; the numerical clauses (i) and (ii) are the theorem conclusion
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.2, PDF/printed p.30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 2; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_2 (eps : ℝ) (heps : 0 < eps ∧ eps < 1) :
    (∀ i < bandCount eps,
      (threshold eps i ≤ 1 ∧ 0 < threshold eps i ∧ 1 ≤ thresholdK eps i ∧
       threshold eps (i+1) ≤ threshold eps i / 2 ∧ threshold eps i / 2 < threshold eps i) ∧
      threshold eps (i+1) ≤ bZero (accuracy eps) (accuracy eps) (thresholdK eps i)) := by sorry

end
end StochMatchQuery.Union
