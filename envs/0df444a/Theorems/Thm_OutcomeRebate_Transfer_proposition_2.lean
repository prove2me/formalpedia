-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_proposition_2
-- name    : OutcomeRebate.Transfer.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:27.383227+00:00
-- url     : https://prove2.me/theorems/f7331db7-a52b-451b-9f61-f1bd1f374915
-- title:
--   Proposition 2, p. 18 (PDF 19) — the payer's coverage decision under outcome-based pricing
-- statement:
--   Under outcome-based pricing:
--
--   (a) if $p \ge \bar v/\beta$, the payer is indifferent about coverage;
--
--   (b) if $0 \le p < \bar v/\beta$, then
--   1. for $p \le \bar v$, the payer covers iff $p \le \bar p_2 = 2v'/(1-\beta)$;
--   2. for $\bar v < p$, the payer covers iff $p \le \bar p_1 = (v' + \bar v/2)/(1-\beta/2)$.
--
--   Unlike uniform pricing, the coverage decision does not depend on the chance of success.
--
--   **Formalization Note** "Covers" means $W^O_{\text{payer}}|_{\bar\beta=\beta} \ge W^O_{\text{payer}}|_{\bar\beta=1}$, the rule $\Delta^O \ge 0$.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 18 (PDF 19), Proposition 2

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Proposition 2 (p. 18). Under outcome-based pricing,
(a) if `p ≥ v̄/β` the payer is indifferent about coverage;
(b) if `0 ≤ p < v̄/β` then
1. for `p ≤ v̄` the payer covers iff `p ≤ p̄₂ = 2v′/(1 − β)`;
2. for `v̄ < p` the payer covers iff `p ≤ p̄₁ = (v′ + v̄/2)/(1 − β/2)`. -/
theorem proposition_2 (P : Params) (hS : P.Standing) :
    (∀ p : ℝ, P.vbar / P.β ≤ p → payerObjO P 1 p = payerObjO P P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / P.β →
      (p ≤ P.vbar → (coversO P p ↔ p ≤ 2 * P.vp / (1 - P.β))) ∧
      (P.vbar < p → (coversO P p ↔ p ≤ (P.vp + P.vbar / 2) / (1 - P.β / 2)))) := by sorry

end OutcomeRebate.Transfer
