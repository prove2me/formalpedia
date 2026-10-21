-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_3_ii_a
-- name    : RefurbCommit.DefectProfit.proposition_3_ii_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:52.25309+00:00
-- url     : https://prove2.me/theorems/5dd7d92b-881f-4e69-bcd0-3d6fd4242e8b
-- title:
--   Proposition 3(ii)(a), p. 14 (PDF 15) — Π* = Π^C for α ≥ αc = (vn − cn)/(cn + h)
-- statement:
--   Fix parameters satisfying the standing assumptions and let
--   $$\alpha_c=\frac{v_n-c_n}{c_n+h}.$$
--   For every defect rate $\alpha>0$ with $\alpha\ge\alpha_c$, the firm's profit without commitment equals its commitment profit:
--   $$\Pi^*(\alpha)=\Pi^C(\alpha).$$
--
--   Above $\alpha_c$ a new unit sold in the second period no longer covers its effective cost ($\mu_n\le0$), so the firm does not offer the new product in period 2 in either setting; the refurbished returns then act as a commitment device.
--
--   **Formalization Note** The page asserts the existence of a threshold; the statement gives the explicit threshold $\alpha_c$ of the proof (p. A-5), a stronger form. When $v_n\le c_n$, $\alpha_c\le0$ and the statement covers every $\alpha>0$.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. 14 (PDF 15), Proposition 3(ii)(a); αc from the proof, p. A-5 (PDF 38)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 3(ii)(a) (p. 14), with `αc = (vn − cn)/(cn + h)` from its proof (p. A-5):
for every defect rate `α ≥ αc`, `Π* = Π^C`. -/
theorem proposition_3_ii_a (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α)
    (hαc : alphaC P ≤ α) :
    PiStar P α = PiC P α := by sorry

end RefurbCommit.DefectProfit
