-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_proposition_6
-- name    : OutcomeRebate.Transfer.Supplement.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:03:59.401105+00:00
-- url     : https://prove2.me/theorems/92a96be8-f136-4a92-9725-51bdfec8b177
-- title:
--   Proposition 6 (corrected: missing bar) — the payer's coverage decision under a partial rebate
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$.
--
--   For a partial rebate, let $0\le\theta\le1$, $m=\theta+q(1-\theta)$ and $\bar z=1+\theta(z-1)$. No profitability assumption is imposed. The payer is indifferent at every price
--
--   $$p\ge\bar v/(\beta\bar z).$$
--
--   For $0\le p<\bar v/(\beta\bar z)$:
--
--   1. If $m\le\beta q\bar z/2$, the payer covers.
--   2. If $\beta q\bar z/2<m\le(1+\beta)q\bar z/2$, it covers all $p\le\bar v/\bar z$; above that point it covers iff $p\le q(v'+\bar v/2)/(m-q\bar z\beta/2)$.
--   3. If $m>(1+\beta)q\bar z/2$, it covers for $p\le\bar v/\bar z$ iff $p\le qv'/(m-q\bar z(1+\beta)/2)$; above that point it covers iff $p\le q(v'+\bar v/2)/(m-q\bar z\beta/2)$.
--
--   Indifference means equality of the two objectives, rather than an arbitrary coverage decision. These thresholds supply the payer stage for Theorem 3.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - correction: part (b) prints p < vbar/(βz) → part (b) uses p < vbar/(β zbar); reason: part (a), all the price intervals and Appendix G on p. 58 use zbar; the printed z is a missing bar
--   - generalization: Appendix C assumes βc/vbar < m/zbar → the coverage proposition imposes no profitability inequality; reason: coverage objectives and their difference do not contain production cost, so the full payer rule extends to all positive costs
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 43 (PDF 44), Proposition 6

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_PartialRebate

namespace OutcomeRebate.Transfer.Supplement

theorem proposition_6 (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    let m := partialMargin P θ
    let zb := zBar P θ
    (∀ p : ℝ, P.vbar / (P.β * zb) ≤ p → payerObjP P θ 1 p = payerObjP P θ P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * zb) →
      (m ≤ P.β * P.q * zb / 2 → coversP P θ p) ∧
      (P.β * P.q * zb / 2 < m → m ≤ (1 + P.β) * P.q * zb / 2 →
        (p ≤ P.vbar / zb → coversP P θ p) ∧
        (P.vbar / zb < p → (coversP P θ p ↔ p ≤ P.q * (P.vp + P.vbar / 2) / (m - P.q * zb * P.β / 2)))) ∧
      ((1 + P.β) * P.q * zb / 2 < m →
        (p ≤ P.vbar / zb → (coversP P θ p ↔ p ≤ P.q * P.vp / (m - P.q * zb * (1 + P.β) / 2))) ∧
        (P.vbar / zb < p → (coversP P θ p ↔ p ≤ P.q * (P.vp + P.vbar / 2) / (m - P.q * zb * P.β / 2))))) := by sorry

end OutcomeRebate.Transfer.Supplement
