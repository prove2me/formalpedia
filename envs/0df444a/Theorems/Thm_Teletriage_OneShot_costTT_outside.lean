-- Prove2me | Theorems.Thm_Teletriage_OneShot_costTT_outside
-- name    : Teletriage.OneShot.costTT_outside
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:00.771329+00:00
-- url     : https://prove2.me/theorems/665c7880-f87f-4f4f-a256-8de7029aa77b
-- title:
--   Proof of Proposition 2, p. ec1 (PDF 26) — teletriage costs c_T + c_E for b ≥ b̿0 and c_T + c_P + b c_E for b ≤ b̲̲0
-- statement:
--   Assume the standing assumptions and informative teletriage, and let $0\le b\le1$. Write
--   $$C_T(b)=c_T+(\alpha b+(1-\beta)(1-b))V_0(b_{PS})+((1-\alpha)b+\beta(1-b))V_0(b_{PC})$$
--   for the expected cost of calling teletriage, the third term of (11). Then
--   1. if $b\ge\bar{\bar b}_0$, then $C_T(b)=c_T+c_E$ (after either prediction the patient goes to the ED);
--   2. if $b\le\underline{\underline b}_0$, then $C_T(b)=c_T+c_P+b\,c_E$ (after either prediction the patient goes to the PCP).
--
--   Outside the middle range, therefore, calling teletriage only adds the copay $c_T$ to the cost of an action the patient could have taken directly.
--
--   **Formalization Note** The second item is the case the page calls analogous and omits.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. ec1 (PDF 26), proof of Proposition 2

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proof of Proposition 2, p. ec1: outside `(b̲̲0, b̿0)` the cost of calling teletriage is
`cT + cE` (above) and `cT + cP + b cE` (below). -/
theorem costTT_outside (P : Params) (hS : P.Standing) (hI : P.Informative) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (bHighHigh P ≤ b → costTT P b = P.cT + P.cE) ∧
    (b ≤ bLowLow P → costTT P b = P.cT + costPCP P b) := by sorry

end Teletriage.OneShot
