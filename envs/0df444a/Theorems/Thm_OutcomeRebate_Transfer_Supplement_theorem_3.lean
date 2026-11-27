-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_theorem_3
-- name    : OutcomeRebate.Transfer.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:04:48.015212+00:00
-- url     : https://prove2.me/theorems/dfc5f35c-f27e-4814-a149-94b9be667b72
-- title:
--   Theorem 3 — equilibrium price and coverage under a partial rebate in all five cases
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$.
--
--   Let $0\le\theta\le1$, $m=\theta+q(1-\theta)$, $\bar z=1+\theta(z-1)$, and assume $\beta c/\bar v<m/\bar z$, without also imposing Assumption 1. Put
--
--   $$a=m-q\bar z\beta/2,\quad b=m-q\bar z(1+\beta)/2,\quad p^{P*}=c/(2m)+\bar v/(2\beta\bar z),\quad\bar p^{P*}=c/(2m)+\bar v/(2\bar z).$$
--
--   If $c/m\le\bar v/\bar z$, there is a unique $p^P_3\in[c/m,\bar p^{P*}]$ solving $\Pi^P_{firm}(\bar p^{P*};1)=\Pi^P_{firm}(p^P_3;\beta)$. The five implications are:
--
--   1. If $m\le\beta q\bar z/2$ or $v'\ge p^{P*}a/q-\bar v/2$, then $p^{P*}$ is the unique covered equilibrium price.
--   2. If $m>\beta q\bar z/2$ and $\max\{c/m,\bar v/\bar z\}a/q-\bar v/2<v'<p^{P*}a/q-\bar v/2$, then $q(v'+\bar v/2)/a$ is the unique covered equilibrium price.
--   3. If $c/m\le\bar v/\bar z$, $m>(1+\beta)q\bar z/2$ and $p^P_3b/q\le v'\le(\bar v/\bar z)a/q-\bar v/2$, then $qv'/b$ is a covered equilibrium price, unique if the lower benefit bound is strict.
--   4. If $c/m\le\bar v/\bar z$, $m>(1+\beta)q\bar z/2$ and $v'<p^P_3b/q$, then $\bar p^{P*}$ is an uncovered equilibrium price, unique if $c/m<\bar v/\bar z$.
--   5. If $c/m>\bar v/\bar z$, $m>\beta q\bar z/2$ and $v'\le(c/q)a/m-\bar v/2$, then every realized profit is at most zero and zero is attained. Coverage is absent on $(c/m,\bar v/(\beta\bar z))$, and also at $c/m$ if the benefit bound is strict.
--
--   The endpoints $\theta=0,1$ are included. These are the five claims of the partial-rebate equilibrium theorem; no additional exhaustiveness assertion is attached.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - reading: the firm prices at X → X is an equilibrium, the coverage decision at X is stated, and uniqueness is conditional at exact profit ties and zero margins; reason: the proof compares covered and uncovered profits; equal profits give multiple maximizing prices, so no uniqueness is claimed at those ties
--   - reading: makes no profit regardless of price and no coverage → realized profit ≤ 0 at every p ≥ 0, with zero attained; no coverage on the stated interval above cost and below the covered demand cutoff, and at cost when the benefit inequality is strict; reason: prices below cost lose money and a zero-demand payer is indifferent and covers; the proof of Theorem 1, pp. 52–53, restricts attention to the nonnegative-margin demand interval
--   - reading: the implicit price is the unique root on the displayed interval → existence and uniqueness are conclusions conditional on the interval being nonempty; root hypotheses occur only in cases 3–4; reason: requiring the root globally would remove high-cost cases 1, 2 and 5
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 43 (PDF 44), Theorem 3

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_PartialRebate

namespace OutcomeRebate.Transfer.Supplement

theorem theorem_3 (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hA : PartialAssumption P θ) :
    let m := partialMargin P θ
    let zb := zBar P θ
    let a := m - P.q * zb * P.β / 2
    let b := m - P.q * zb * (1 + P.β) / 2
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc (P.c / m) (pPartialBarStar P θ) ∧
      firmProfitP P θ 1 (pPartialBarStar P θ) = firmProfitP P θ P.β p3
    let p1 := P.q * (P.vp + P.vbar / 2) / a
    let p2 := P.q * P.vp / b
    (P.c / m ≤ P.vbar / zb → ∃! p3, rootP p3) ∧
    ((m ≤ P.β * P.q * zb / 2 ∨ pPartialStar P θ * a / P.q - P.vbar / 2 ≤ P.vp) →
      IsEqPriceP P θ (pPartialStar P θ) ∧ coversP P θ (pPartialStar P θ) ∧
      ∀ p, IsEqPriceP P θ p → p = pPartialStar P θ) ∧
    ((P.β * P.q * zb / 2 < m ∧ max (P.c / m) (P.vbar / zb) * a / P.q - P.vbar / 2 < P.vp ∧
      P.vp < pPartialStar P θ * a / P.q - P.vbar / 2) →
      IsEqPriceP P θ p1 ∧ coversP P θ p1 ∧ ∀ p, IsEqPriceP P θ p → p = p1) ∧
    (∀ p3, rootP p3 →
      ((P.c / m ≤ P.vbar / zb ∧ (1 + P.β) * P.q * zb / 2 < m ∧
        p3 * b / P.q ≤ P.vp ∧ P.vp ≤ P.vbar / zb * a / P.q - P.vbar / 2) →
        IsEqPriceP P θ p2 ∧ coversP P θ p2 ∧
        (p3 * b / P.q < P.vp → ∀ p, IsEqPriceP P θ p → p = p2)) ∧
      ((P.c / m ≤ P.vbar / zb ∧ (1 + P.β) * P.q * zb / 2 < m ∧ P.vp < p3 * b / P.q) →
        IsEqPriceP P θ (pPartialBarStar P θ) ∧ ¬coversP P θ (pPartialBarStar P θ) ∧
        (P.c / m < P.vbar / zb → ∀ p, IsEqPriceP P θ p → p = pPartialBarStar P θ))) ∧
    ((P.vbar / zb < P.c / m ∧ P.β * P.q * zb / 2 < m ∧ P.vp ≤ (P.c / P.q) * a / m - P.vbar / 2) →
      (∀ p, 0 ≤ p → realizedProfitP P θ p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitP P θ p = 0) ∧
      (∀ p, P.c / m < p → p < P.vbar / (P.β * zb) → ¬coversP P θ p) ∧
      (P.vp < (P.c / P.q) * a / m - P.vbar / 2 → ¬coversP P θ (P.c / m))) := by sorry

end OutcomeRebate.Transfer.Supplement
