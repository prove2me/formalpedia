-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_3_i
-- name    : RefurbCommit.DefectProfit.proposition_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:00.824422+00:00
-- url     : https://prove2.me/theorems/e943783f-b677-459a-8716-f6e40ef67b94
-- title:
--   Proposition 3(i), p. 14 (PDF 15) — the commitment profit Π^C strictly decreases in the defect rate α
-- statement:
--   Fix parameters satisfying the standing assumptions. On the set of defect rates at which the commitment profit is positive, $\{\alpha>0:\Pi^C(\alpha)>0\}$, the commitment profit is strictly decreasing:
--   $$0<\alpha<\alpha',\ \Pi^C(\alpha)>0,\ \Pi^C(\alpha')>0\ \Longrightarrow\ \Pi^C(\alpha')<\Pi^C(\alpha).$$
--
--   If the firm could commit to its future prices, defects would only add friction (production of replacements, refurbishing cost, hassle cost), so profit falls with the defect rate. This is the benchmark against which part (ii)(b) of Proposition 3 is surprising.
--
--   **Formalization Note** "Monotonically decrease" is read as strict decrease on the paper's positive-profit region (p. 6); where $\Pi^C=0$ nothing is sold. A weak reading would be satisfied by a constant function.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. 14 (PDF 15), Proposition 3(i); proof pp. A-4–A-5 (PDF 37–38)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 3(i) (p. 14): the commitment profit `Π^C` is strictly decreasing in the
defect rate on the positive-profit region `{α > 0 | Π^C(α) > 0}`. -/
theorem proposition_3_i (P : Params) (hP : P.Standing) :
    StrictAntiOn (PiC P) {α | 0 < α ∧ 0 < PiC P α} := by sorry

end RefurbCommit.DefectProfit
