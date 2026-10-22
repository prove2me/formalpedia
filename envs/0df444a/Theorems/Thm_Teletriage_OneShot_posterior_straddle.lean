-- Prove2me | Theorems.Thm_Teletriage_OneShot_posterior_straddle
-- name    : Teletriage.OneShot.posterior_straddle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:50.334606+00:00
-- url     : https://prove2.me/theorems/2765d225-a7d5-4555-bea1-92511a994354
-- title:
--   Proof of Proposition 2, p. ec1 (PDF 26) — b̲̲0 ≤ b̲0, b̄0 ≤ b̿0, and where the posteriors b_PS, b_PC fall relative to b0
-- statement:
--   Assume the standing assumptions and informative teletriage, $\alpha+\beta<1$. With $b_0=1-c_P/c_E$, the thresholds $\underline b_0,\bar b_0$ of (14), and
--   $$\underline{\underline b}_0=\frac{\beta b_0}{\beta b_0+(1-\alpha)(1-b_0)},\qquad \bar{\bar b}_0=\frac{(1-\beta)b_0}{(1-\beta)b_0+\alpha(1-b_0)},$$
--   the following hold.
--   1. $\underline{\underline b}_0\le\underline b_0$ and $\bar b_0\le\bar{\bar b}_0$.
--   2. If $0\le b<1$ and $b\ge\bar{\bar b}_0$, then $b_{PS}\ge b_0$.
--   3. If $0\le b\le 1$ and $b\le\underline{\underline b}_0$, then $b_{PC}\le b_0$.
--   4. If $0\le b\le1$ and $\underline{\underline b}_0<b<\bar{\bar b}_0$, then $b_{PS}<b_0<b_{PC}$.
--
--   These facts split the beliefs into the three ranges used in the proof of Proposition 2: above $\bar{\bar b}_0$ both posteriors lead to the ED, below $\underline{\underline b}_0$ both lead to the PCP, and in between the prediction decides.
--
--   **Formalization Note** The page gives non-strict inequalities in item 4; on the open range they are strict, which is what the probability display of p. 11 needs. The case $b\le\underline{\underline b}_0$ is "analogous" on the page and is stated here explicitly. Item 2 excludes $b=1$, where $b_{PS}$ is $0/0$ when $\alpha=0$.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. ec1 (PDF 26), proof of Proposition 2

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proof of Proposition 2, p. ec1: `b̲̲0 ≤ b̲0`, `b̄0 ≤ b̿0`, and the position of the posteriors
relative to `b0` in the three belief ranges cut by `b̲̲0` and `b̿0`. -/
theorem posterior_straddle (P : Params) (hS : P.Standing) (hI : P.Informative) :
    (bLowLow P ≤ bLow P ∧ bHigh P ≤ bHighHigh P) ∧
    (∀ b : ℝ, 0 ≤ b → b < 1 → bHighHigh P ≤ b → b0 P ≤ bPS P b) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → b ≤ bLowLow P → bPC P b ≤ b0 P) ∧
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 → bLowLow P < b → b < bHighHigh P →
      bPS P b < b0 P ∧ b0 P < bPC P b) := by sorry

end Teletriage.OneShot
