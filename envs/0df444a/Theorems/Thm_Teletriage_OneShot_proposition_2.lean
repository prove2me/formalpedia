-- Prove2me | Theorems.Thm_Teletriage_OneShot_proposition_2
-- name    : Teletriage.OneShot.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:00.240543+00:00
-- url     : https://prove2.me/theorems/fef06d7a-ca90-4e71-a5fb-44b2d030d0d3
-- title:
--   Proposition 2, p. 10 (PDF 10) — informative teletriage: PCP below b̲0, teletriage between b̲0 and b̄0, ED from b̄0 on
-- statement:
--   Assume the standing assumptions and that teletriage is informative, $\alpha+\beta<1$, and define $\underline b_0$ and $\bar b_0$ by (14). Let $0\le b\le1$ and write $C_T(b)$ for the expected cost of calling teletriage (third term of (11)).
--
--   1. Suppose $\underline b_0<\bar b_0$. Then
--      - if $b<\underline b_0$, the PCP is optimal: $c_P+b\,c_E<c_E$ and $c_P+b\,c_E\le C_T(b)$;
--      - if $\underline b_0<b<\bar b_0$, the patient calls teletriage, and teletriage is strictly cheaper than both providers: $C_T(b)<c_E$ and $C_T(b)<c_P+b\,c_E$;
--      - if $b\ge\bar b_0$, the patient goes to the ED.
--   2. If $\underline b_0\ge\bar b_0$, no patient calls teletriage. More precisely,
--   $$\min\{c_E,\;c_P+b\,c_E\}\ \le\ C_T(b),$$
--   and the model's tie rule does not select teletriage.
--
--   This is the complete characterization of the patient's optimal one-shot decision when teletriage is available.
--
--   **Formalization Note** The page's "if and only if" claims each endpoint for two actions; at $c_T=0$ teletriage ties the PCP for every $b\le\underline{\underline b}_0$, so a literal "PCP iff $b\le\underline b_0$" is false under any tie rule. The statement is therefore the strict open-region reading: optimality of the PCP below $\underline b_0$, strict optimality of teletriage strictly between the thresholds, and the ED (whose tie rule ED ≻ teletriage ≻ PCP is fixed by the model) from $\bar b_0$ on. The last clause states the page's "no patient uses teletriage" under that tie rule.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 10 (PDF 10), Proposition 2, (14)

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proposition 2, p. 10, in its strict open-region reading: if `b̲0 < b̄0`, the PCP is optimal
below `b̲0`, teletriage is the strictly optimal action strictly between `b̲0` and `b̄0`, and the
ED is optimal from `b̄0` on; if `b̲0 ≥ b̄0`, no patient calls teletriage. -/
theorem proposition_2 (P : Params) (hS : P.Standing) (hI : P.Informative) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (bLow P < bHigh P →
      (b < bLow P → costPCP P b < P.cE ∧ costPCP P b ≤ costTT P b) ∧
      (bLow P < b → b < bHigh P →
        actTT P b = .TT ∧ costTT P b < P.cE ∧ costTT P b < costPCP P b) ∧
      (bHigh P ≤ b → actTT P b = .ED)) ∧
    (bHigh P ≤ bLow P →
      min P.cE (costPCP P b) ≤ costTT P b ∧ actTT P b ≠ .TT) := by sorry

end Teletriage.OneShot
