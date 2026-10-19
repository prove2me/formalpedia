-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_proposition_1
-- name    : OutcomeRebate.Transfer.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:37.437384+00:00
-- url     : https://prove2.me/theorems/221b1fd2-a5a5-4db1-91ae-ef86cad4493d
-- title:
--   Proposition 1, p. 15 (PDF 16) — the payer's coverage decision under uniform pricing
-- statement:
--   Under uniform pricing, let $q_1 \in (0,1)$ solve $zq = 2/\beta$ and $q_2 \in (0,1)$ solve $zq = 2/(1+\beta)$. Put
--   $$p_1 = \frac{q(v' + \bar v/2)}{1 - qz\beta/2}, \qquad p_2 = \frac{q v'}{1 - qz(1+\beta)/2}.$$
--   Then $q_1 < q_2 < q_0$, and:
--
--   (a) if $p \ge \bar v/(\beta z)$, the payer is indifferent about coverage (its objective is the same with and without coverage);
--
--   (b) if $0 \le p < \bar v/(\beta z)$, then
--   1. if $q \le q_1$, the payer covers the drug;
--   2. if $q_1 < q \le q_2$, the payer covers the drug for $p \le \bar v/z$, and for $p > \bar v/z$ it covers iff $p \le p_1$;
--   3. if $q > q_2$, for $p \le \bar v/z$ it covers iff $p \le p_2$, and for $p > \bar v/z$ it covers iff $p \le p_1$.
--
--   The payer covers a risky drug at any price, and covers a safer drug only below a price threshold.
--
--   **Formalization Note** "Covers" means $W^U_{\text{payer}}|_{\bar\beta=\beta} \ge W^U_{\text{payer}}|_{\bar\beta=1}$, the rule $\Delta^U \ge 0$ of the paper's proof. The roots $q_1$, $q_2$ are passed as hypotheses. The page's "$q_1 \in (0,q_2)$" and "$q_2 \in (0,q_0)$" are conclusions here, and uniqueness of the roots is the milestone `zq_monotone`.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 15 (PDF 16), Proposition 1; coverage rule from its proof, p. 50 (PDF 51)

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Proposition 1 (p. 15). Under uniform pricing, with `q₁` the solution of `zq = 2/β` and `q₂` the
solution of `zq = 2/(1 + β)` on `(0, 1)`:
(a) if `p ≥ v̄/(βz)` the payer is indifferent about coverage;
(b) if `0 ≤ p < v̄/(βz)` then
1. if `q ≤ q₁` the payer covers the drug;
2. if `q₁ < q ≤ q₂` the payer covers for `p ≤ v̄/z`, and for `p > v̄/z` covers iff `p ≤ p₁`;
3. if `q > q₂`, for `p ≤ v̄/z` the payer covers iff `p ≤ p₂`, and for `p > v̄/z` iff `p ≤ p₁`,
where `p₁ = q(v′ + v̄/2)/(1 − qzβ/2)` and `p₂ = qv′/(1 − qz(1 + β)/2)`. Moreover `q₁ < q₂ < q₀`. -/
theorem proposition_1 (P : Params) (hS : P.Standing) (q1 q2 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β)
    (hq2 : 0 < q2 ∧ q2 < 1 ∧ zOf P.α P.lam q2 * q2 = 2 / (1 + P.β)) :
    let p1 := P.q * (P.vp + P.vbar / 2) / (1 - P.q * P.z * P.β / 2)
    let p2 := P.q * P.vp / (1 - P.q * P.z * (1 + P.β) / 2)
    (q1 < q2 ∧ q2 < q0 P.α P.lam) ∧
    (∀ p : ℝ, P.vbar / (P.β * P.z) ≤ p → payerObjU P 1 p = payerObjU P P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * P.z) →
      (P.q ≤ q1 → coversU P p) ∧
      (q1 < P.q → P.q ≤ q2 →
        (p ≤ P.vbar / P.z → coversU P p) ∧ (P.vbar / P.z < p → (coversU P p ↔ p ≤ p1))) ∧
      (q2 < P.q →
        (p ≤ P.vbar / P.z → (coversU P p ↔ p ≤ p2)) ∧
          (P.vbar / P.z < p → (coversU P p ↔ p ≤ p1)))) := by sorry

end OutcomeRebate.Transfer
