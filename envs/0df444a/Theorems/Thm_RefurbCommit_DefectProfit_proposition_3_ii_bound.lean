-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_3_ii_bound
-- name    : RefurbCommit.DefectProfit.proposition_3_ii_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:50.776625+00:00
-- url     : https://prove2.me/theorems/42c99db3-c319-4097-8f44-92e4074d27ed
-- title:
--   Proposition 3(ii), p. 14 (PDF 15) — Π* ≤ Π^C
-- statement:
--   Fix parameters satisfying the standing assumptions and a defect rate $\alpha>0$. The firm's subgame-perfect profit without commitment is at most its commitment profit:
--   $$\Pi^*(\alpha)\le\Pi^C(\alpha).$$
--
--   This is the time-inconsistency cost of Coase and Bulow: the inability to commit to future prices can only lower profit.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. 14 (PDF 15), Proposition 3(ii); proof p. A-5 (PDF 38)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 3(ii), first clause (p. 14): `Π* ≤ Π^C` for every defect rate `α > 0`. -/
theorem proposition_3_ii_bound (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) :
    PiStar P α ≤ PiC P α := by sorry

end RefurbCommit.DefectProfit
