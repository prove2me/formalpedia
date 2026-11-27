-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_theorem_4
-- name    : OutcomeRebate.Transfer.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:06:08.82275+00:00
-- url     : https://prove2.me/theorems/8bf53cb3-760a-4791-a978-320e2f4ad297
-- title:
--   Theorem 4 — equilibrium price and coverage under uniform pricing when v′ = kv
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. Assume Assumption 1, $\beta c/\bar v<\min\{q,1/z\}$. Let $k>0$ and replace payer benefit by $kv$; the old $v'$ coordinate is unused. For uniform pricing define
--
--   $$A=\frac{2}{\beta qz}\frac{\bar v+c\beta z}{3\bar v+c\beta z},\quad B=\frac2{q(\beta z+\bar v/\max\{c,\bar v/z\})},\quad\hat p_1=\frac{\bar vq(k+1)}{2-\beta zq(k+1)},$$
--   $$p^*=c/2+\bar v/(2\beta z),\qquad\bar p^*=c/2+\bar v/(2z).$$
--
--   1. If $k+1\ge A$, then $p^*$ is the unique covered equilibrium price.
--   2. If $B\le k+1<A$, then $\hat p_1$ is a covered equilibrium price, unique if $\hat p_1>c$.
--   3. If $k+1<B$ and $c\le \bar v/z$, then $\bar p^*$ is an uncovered equilibrium price, unique if the cost inequality is strict.
--   4. If $k+1<B$ and $c>\bar v/z$, then every nonnegative price has realized profit at most zero, zero is attained, and coverage is absent for $c\le p<\bar v/(\beta z)$.
--
--   This gives all four implications for the firm's optimal price under a perfectly correlated payer benefit, including the equality $k+1=B$ in case 2.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - reading: the firm prices at X → X is an equilibrium, the coverage decision at X is stated, and uniqueness is conditional at exact profit ties and zero margins; reason: the proof compares covered and uncovered profits; equal profits give multiple maximizing prices, so no uniqueness is claimed at those ties
--   - reading: makes no profit regardless of price and no coverage → realized profit ≤ 0 at every p ≥ 0, with zero attained; no coverage on the stated interval above cost and below the covered demand cutoff, and at cost when the benefit inequality is strict; reason: prices below cost lose money and a zero-demand payer is indifferent and covers; the proof of Theorem 1, pp. 52–53, restricts attention to the nonnegative-margin demand interval
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 48 (PDF 49), Theorem 4

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
import Definitions.Def_OutcomeRebate_Transfer_Supplement_UniformPrices

namespace OutcomeRebate.Transfer.Supplement

theorem theorem_4 (P : Params) (hS : P.Standing) (hA : Assumption1 P) (k : ℝ) (hk : 0 < k) :
    (thresholdA P ≤ k + 1 → IsEqPriceKU P k (pStar P) ∧ coversKU P k (pStar P) ∧
      ∀ p, IsEqPriceKU P k p → p = pStar P) ∧
    (thresholdB P ≤ k + 1 → k + 1 < thresholdA P →
      IsEqPriceKU P k (pHat1 P k) ∧ coversKU P k (pHat1 P k) ∧
      (P.c < pHat1 P k → ∀ p, IsEqPriceKU P k p → p = pHat1 P k)) ∧
    (k + 1 < thresholdB P → P.c ≤ P.vbar / P.z →
      IsEqPriceKU P k (pBarStar P) ∧ ¬coversKU P k (pBarStar P) ∧
      (P.c < P.vbar / P.z → ∀ p, IsEqPriceKU P k p → p = pBarStar P)) ∧
    (k + 1 < thresholdB P → P.vbar / P.z < P.c →
      (∀ p, 0 ≤ p → realizedProfitKU P k p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitKU P k p = 0) ∧
      (∀ p, P.c ≤ p → p < P.vbar / (P.β * P.z) → ¬coversKU P k p)) := by sorry

end OutcomeRebate.Transfer.Supplement
