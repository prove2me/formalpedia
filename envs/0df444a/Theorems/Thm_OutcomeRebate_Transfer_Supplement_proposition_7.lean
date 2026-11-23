-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_proposition_7
-- name    : OutcomeRebate.Transfer.Supplement.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:05:29.397401+00:00
-- url     : https://prove2.me/theorems/c51252a6-d088-4f9c-b51b-dbb54504c2c5
-- title:
--   Proposition 7 (corrected: zero-price coverage) — the payer's coverage decision under uniform pricing when v′ = kv
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. In Appendix F let $k>0$ and use payer benefit $kv$ in place of $v'$. The old constant $v'$ is unused. No Assumption 1 is required. In uniform pricing the payer is indifferent for
--
--   $$p\ge \bar v/(\beta z).$$
--
--   For $0\le p<\bar v/(\beta z)$:
--
--   1. If $k+1\ge 1/(qz\beta)$, the payer covers.
--   2. If $2/(qz(\beta+1))\le k+1<1/(qz\beta)$, the payer covers all $p\le \bar v/z$; above that point it covers iff $p\le \hat p_1$, where $\hat p_1=\bar vq(k+1)/(2-\beta zq(k+1))$.
--   3. If $k+1<2/(qz(\beta+1))$ and $p>0$, the payer does not cover.
--
--   At $p=0$ the payer covers, including case 3. This explicit boundary follows the weak coverage comparison. These assertions describe the payer response used in Theorem 4.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - correction: case (b)3 says no coverage → no coverage for strictly positive prices; coverage at p = 0 is explicit; reason: both objectives agree at zero and the paper defines coverage by a weak comparison; the p² formula in the proof on p. 59 gives equality at zero
--   - generalization: the pricing section carries Assumption 1 → the payer-coverage proposition does not require Assumption 1; reason: production cost does not enter either payer objective and is unrestricted by the coverage comparison
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 48 (PDF 49), Proposition 7

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit

namespace OutcomeRebate.Transfer.Supplement

theorem proposition_7 (P : Params) (hS : P.Standing) (k : ℝ) (hk : 0 < k) :
    (∀ p : ℝ, P.vbar / (P.β * P.z) ≤ p → payerObjKU P k 1 p = payerObjKU P k P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * P.z) →
      (1 / (P.q * P.z * P.β) ≤ k + 1 → coversKU P k p) ∧
      (2 / (P.q * P.z * (P.β + 1)) ≤ k + 1 → k + 1 < 1 / (P.q * P.z * P.β) →
        (p ≤ P.vbar / P.z → coversKU P k p) ∧
        (P.vbar / P.z < p → (coversKU P k p ↔ p ≤ pHat1 P k))) ∧
      (k + 1 < 2 / (P.q * P.z * (P.β + 1)) → 0 < p → ¬coversKU P k p)) ∧
    coversKU P k 0 := by sorry

end OutcomeRebate.Transfer.Supplement
