-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_proposition_8
-- name    : OutcomeRebate.Transfer.Supplement.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:06:38.473977+00:00
-- url     : https://prove2.me/theorems/824b2290-d2ef-45e5-acf4-3837ba492d08
-- title:
--   Proposition 8 (corrected: zero-price coverage) — the payer's coverage decision under outcome-based pricing when v′ = kv
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. In Appendix F let $k>0$ and use payer benefit $kv$ in place of $v'$. The old constant $v'$ is unused. No Assumption 1 is required. In outcome-based pricing the payer is indifferent for
--
--   $$p\ge \bar v/\beta.$$
--
--   For $0\le p<\bar v/\beta$:
--
--   1. If $k+1\ge 1/\beta$, the payer covers.
--   2. If $2/(\beta+1)\le k+1<1/\beta$, the payer covers all $p\le \bar v$; above that point it covers iff $p\le \hat p_2$, where $\hat p_2=\bar v(k+1)/(2-\beta(k+1))$.
--   3. If $k+1<2/(\beta+1)$ and $p>0$, the payer does not cover.
--
--   At $p=0$ the payer covers, including case 3. This explicit boundary follows the weak coverage comparison. These assertions describe the payer response used in Theorem 5.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - correction: case (b)3 says no coverage → no coverage for strictly positive prices; coverage at p = 0 is explicit; reason: both objectives agree at zero and the paper defines coverage by a weak comparison; the p² formula in the proof on p. 59 gives equality at zero
--   - generalization: the pricing section carries Assumption 1 → the payer-coverage proposition does not require Assumption 1; reason: production cost does not enter either payer objective and is unrestricted by the coverage comparison
--   - reading: Appendix F.2 prints outcome demand with a stray z → the published outcome-based buyers and demand have no z; reason: §3.2.1, the patient payoff and the firm profit on p. 49 agree on the threshold βbar p; the proof of Proposition 8 has the same stray factors
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 49 (PDF 50), Proposition 8

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit

namespace OutcomeRebate.Transfer.Supplement

theorem proposition_8 (P : Params) (hS : P.Standing) (k : ℝ) (hk : 0 < k) :
    (∀ p : ℝ, P.vbar / P.β ≤ p → payerObjKO P k 1 p = payerObjKO P k P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / P.β →
      (1 / P.β ≤ k + 1 → coversKO P k p) ∧
      (2 / (P.β + 1) ≤ k + 1 → k + 1 < 1 / P.β →
        (p ≤ P.vbar → coversKO P k p) ∧
        (P.vbar < p → (coversKO P k p ↔ p ≤ pHat2 P k))) ∧
      (k + 1 < 2 / (P.β + 1) → 0 < p → ¬coversKO P k p)) ∧
    coversKO P k 0 := by sorry

end OutcomeRebate.Transfer.Supplement
