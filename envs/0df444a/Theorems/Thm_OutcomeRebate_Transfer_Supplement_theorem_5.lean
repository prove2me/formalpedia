-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_theorem_5
-- name    : OutcomeRebate.Transfer.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:07:24.586249+00:00
-- url     : https://prove2.me/theorems/adb88f27-b930-4c89-8001-b2d8d3056b95
-- title:
--   Theorem 5 — equilibrium price and coverage under outcome-based pricing when v′ = kv
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. Assume Assumption 1, $\beta c/\bar v<\min\{q,1/z\}$. Let $k>0$ and replace payer benefit by $kv$; the old $v'$ coordinate is unused. For outcome-based pricing define
--
--   $$A'=\frac2\beta\frac{\bar vq+\beta c}{3\bar vq+\beta c},\quad B'=\frac2{\beta+\bar v/\max\{c/q,\bar v\}},\quad\hat p_2=\frac{\bar v(k+1)}{2-\beta(k+1)},$$
--   $$\tilde p^*=c/(2q)+\bar v/(2\beta),\qquad\hat p^*=c/(2q)+\bar v/2.$$
--
--   1. If $k+1\ge A'$, then $\tilde p^*$ is the unique covered equilibrium price.
--   2. If $B'\le k+1<A'$, then $\hat p_2$ is a covered equilibrium price, unique if $\hat p_2>c/q$.
--   3. If $k+1<B'$ and $c/q\le \bar v$, then $\hat p^*$ is an uncovered equilibrium price, unique if the cost inequality is strict.
--   4. If $k+1<B'$ and $c/q>\bar v$, then every nonnegative price has realized profit at most zero, zero is attained, and coverage is absent for $c/q\le p<\bar v/\beta$.
--
--   This gives all four implications for the firm's optimal price under a perfectly correlated payer benefit, including the equality $k+1=B'$ in case 2.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - reading: the firm prices at X → X is an equilibrium, the coverage decision at X is stated, and uniqueness is conditional at exact profit ties and zero margins; reason: the proof compares covered and uncovered profits; equal profits give multiple maximizing prices, so no uniqueness is claimed at those ties
--   - reading: makes no profit regardless of price and no coverage → realized profit ≤ 0 at every p ≥ 0, with zero attained; no coverage on the stated interval above cost and below the covered demand cutoff, and at cost when the benefit inequality is strict; reason: prices below cost lose money and a zero-demand payer is indifferent and covers; the proof of Theorem 1, pp. 52–53, restricts attention to the nonnegative-margin demand interval
--   - reading: Appendix F.2 prints outcome demand with a stray z → the published outcome-based buyers and demand have no z; reason: §3.2.1, the patient payoff and the firm profit on p. 49 agree on the threshold βbar p; the proof of Proposition 8 has the same stray factors
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 49 (PDF 50), Theorem 5

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
import Definitions.Def_OutcomeRebate_Transfer_Supplement_OutcomePrices

namespace OutcomeRebate.Transfer.Supplement

theorem theorem_5 (P : Params) (hS : P.Standing) (hA : Assumption1 P) (k : ℝ) (hk : 0 < k) :
    (thresholdAPrime P ≤ k + 1 → IsEqPriceKO P k (pTilde P) ∧ coversKO P k (pTilde P) ∧
      ∀ p, IsEqPriceKO P k p → p = pTilde P) ∧
    (thresholdBPrime P ≤ k + 1 → k + 1 < thresholdAPrime P →
      IsEqPriceKO P k (pHat2 P k) ∧ coversKO P k (pHat2 P k) ∧
      ((P.c / P.q) < pHat2 P k → ∀ p, IsEqPriceKO P k p → p = pHat2 P k)) ∧
    (k + 1 < thresholdBPrime P → (P.c / P.q) ≤ P.vbar →
      IsEqPriceKO P k (pHatStar P) ∧ ¬coversKO P k (pHatStar P) ∧
      ((P.c / P.q) < P.vbar → ∀ p, IsEqPriceKO P k p → p = pHatStar P)) ∧
    (k + 1 < thresholdBPrime P → P.vbar < (P.c / P.q) →
      (∀ p, 0 ≤ p → realizedProfitKO P k p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitKO P k p = 0) ∧
      (∀ p, (P.c / P.q) ≤ p → p < P.vbar / P.β → ¬coversKO P k p)) := by sorry

end OutcomeRebate.Transfer.Supplement
