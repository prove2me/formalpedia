-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_theorem_2
-- name    : OutcomeRebate.Transfer.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:03:14.4948+00:00
-- url     : https://prove2.me/theorems/93a8f39f-2074-4c32-98fe-1df352e9bf37
-- title:
--   Theorem 2 — equilibrium price and coverage under outcome-based pricing in all five cases
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. Assume Assumption 1, $\beta c/\bar v<\min\{q,1/z\}$.
--
--   Define
--
--   $$\tilde p^*=c/(2q)+\bar v/(2\beta),\quad\hat p^*=c/(2q)+\bar v/2,\quad\bar p_1=\frac{v'+\bar v/2}{1-\beta/2},\quad\bar p_2=\frac{2v'}{1-\beta}.$$
--
--   If $c/q\le\bar v$, a unique $\bar p_3\in[c/q,\hat p^*]$ satisfies $\Pi^O_{firm}(\hat p^*;1)=\Pi^O_{firm}(\bar p_3;\beta)$. All five assertions hold:
--
--   1. If $v'\ge\tilde p^*(1-\beta/2)-\bar v/2$, then $\tilde p^*$ is the unique covered equilibrium price.
--   2. If $\max\{c/q,\bar v\}(1-\beta/2)-\bar v/2<v'<\tilde p^*(1-\beta/2)-\bar v/2$, then $\bar p_1$ is the unique covered equilibrium price.
--   3. If $c/q\le\bar v$ and $\bar p_3(1-\beta)/2\le v'\le\bar v(1-\beta)/2$, then $\bar p_2$ is a covered equilibrium price, unique if the lower benefit bound is strict.
--   4. If $c/q\le\bar v$ and $v'<\bar p_3(1-\beta)/2$, then $\hat p^*$ is an uncovered equilibrium price, unique if $c/q<\bar v$.
--   5. If $c/q>\bar v$ and $v'\le(c/q)(1-\beta/2)-\bar v/2$, then every realized profit is at most zero and zero is attained. Coverage is absent on $(c/q,\bar v/\beta)$, and at $c/q$ if the benefit bound is strict.
--
--   Failure of the conditions in all of cases 1–4 is equivalent to the explicit condition of case 5. Thus the word “else” is a mathematical equivalence in the formal statement, including costs for which the implicit-root interval is empty. This is the complete outcome-based equilibrium classification.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - reading: the firm prices at X → X is an equilibrium, the coverage decision at X is stated, and uniqueness is conditional at exact profit ties and zero margins; reason: the proof compares covered and uncovered profits; equal profits give multiple maximizing prices, so no uniqueness is claimed at those ties
--   - reading: makes no profit regardless of price and no coverage → realized profit ≤ 0 at every p ≥ 0, with zero attained; no coverage on the stated interval above cost and below the covered demand cutoff, and at cost when the benefit inequality is strict; reason: prices below cost lose money and a zero-demand payer is indifferent and covers; the proof of Theorem 1, pp. 52–53, restricts attention to the nonnegative-margin demand interval
--   - reading: the implicit price is the unique root on the displayed interval → existence and uniqueness are conclusions conditional on the interval being nonempty; root hypotheses occur only in cases 3–4; reason: requiring the root globally would remove high-cost cases 1, 2 and 5
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 19 (PDF 20), Theorem 2

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_OutcomePrices

namespace OutcomeRebate.Transfer.Supplement

theorem theorem_2 (P : Params) (hS : P.Standing) (hA : Assumption1 P) :
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc (P.c / P.q) (pHatStar P) ∧
      firmProfitO P 1 (pHatStar P) = firmProfitO P P.β p3
    let a := 1 - P.β / 2
    let b := (1 - P.β) / 2
    let p1 := (P.vp + P.vbar / 2) / a
    let p2 := 2 * P.vp / (1 - P.β)
    let C1 := pTilde P * a - P.vbar / 2 ≤ P.vp
    let C2 := max (P.c / P.q) P.vbar * a - P.vbar / 2 < P.vp ∧ P.vp < pTilde P * a - P.vbar / 2
    let C3 := fun p3 => P.c / P.q ≤ P.vbar ∧ p3 * b ≤ P.vp ∧ P.vp ≤ P.vbar * b
    let C4 := fun p3 => P.c / P.q ≤ P.vbar ∧ P.vp < p3 * b
    let C5 := P.vbar < P.c / P.q ∧ P.vp ≤ P.c / P.q * a - P.vbar / 2
    (P.c / P.q ≤ P.vbar → ∃! p3, rootP p3) ∧
    (C1 → IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧ ∀ p, IsEqPriceO P p → p = pTilde P) ∧
    (C2 → IsEqPriceO P p1 ∧ coversO P p1 ∧ ∀ p, IsEqPriceO P p → p = p1) ∧
    (∀ p3, rootP p3 →
      (C3 p3 → IsEqPriceO P p2 ∧ coversO P p2 ∧
        (p3 * b < P.vp → ∀ p, IsEqPriceO P p → p = p2)) ∧
      (C4 p3 → IsEqPriceO P (pHatStar P) ∧ ¬coversO P (pHatStar P) ∧
        (P.c / P.q < P.vbar → ∀ p, IsEqPriceO P p → p = pHatStar P))) ∧
    (C5 → (∀ p, 0 ≤ p → realizedProfitO P p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitO P p = 0) ∧
      (∀ p, P.c / P.q < p → p < P.vbar / P.β → ¬coversO P p) ∧
      (P.vp < P.c / P.q * a - P.vbar / 2 → ¬coversO P (P.c / P.q))) ∧
    ((¬C1 ∧ ¬C2 ∧ ¬(∃ p3, rootP p3 ∧ C3 p3) ∧ ¬(∃ p3, rootP p3 ∧ C4 p3)) ↔ C5) := by sorry

end OutcomeRebate.Transfer.Supplement
