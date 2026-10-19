-- Prove2me | Theorems.Thm_Teletriage_OneShot_middle_comparisons
-- name    : Teletriage.OneShot.middle_comparisons
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:06.788871+00:00
-- url     : https://prove2.me/theorems/e01a5e43-0d81-4e37-9a6e-e2a4e7bba273
-- title:
--   Proof of Proposition 2, p. ec1 (PDF 26) — for b̲̲0 ≤ b ≤ b̿0, teletriage beats the ED iff b < b̄0 and the PCP iff b > b̲0
-- statement:
--   Assume the standing assumptions and informative teletriage, and let $0\le b\le 1$ with $\underline{\underline b}_0\le b\le\bar{\bar b}_0$. Let $C_T(b)$ be the expected cost of calling teletriage, the third term of (11). Then
--   $$C_T(b)<c_E\iff b<\bar b_0,\qquad\qquad C_T(b)<c_P+b\,c_E\iff b>\underline b_0 .$$
--
--   In this middle range the patient goes to the PCP after the prediction *sick* and to the ED after *critical*, so $C_T$ is linear in $b$ and the two comparisons reduce to the thresholds (14).
--
--   **Formalization Note** The page writes the PCP cost on the right-hand side of the second comparison as $c_P+b_{PS}c_E$; the PCP cost at belief $b$ is $c_P+b\,c_E$, which is what is stated here (a typographical slip on the page).
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. ec1 (PDF 26), proof of Proposition 2

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proof of Proposition 2, p. ec1: for `b̲̲0 ≤ b ≤ b̿0`, teletriage is strictly cheaper than the
ED iff `b < b̄0`, and strictly cheaper than the PCP iff `b > b̲0`. -/
theorem middle_comparisons (P : Params) (hS : P.Standing) (hI : P.Informative) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hlo : bLowLow P ≤ b) (hhi : b ≤ bHighHigh P) :
    (costTT P b < P.cE ↔ b < bHigh P) ∧ (costTT P b < costPCP P b ↔ bLow P < b) := by sorry

end Teletriage.OneShot
