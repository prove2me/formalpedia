-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_Supplement_theorem_1
-- name    : OutcomeRebate.Transfer.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:02:40.60216+00:00
-- url     : https://prove2.me/theorems/392f0c6f-0c57-428e-b752-dce45ec23b7a
-- title:
--   Theorem 1 (corrected: exhaustiveness boundary) — equilibrium price and coverage under uniform pricing in all five cases
-- statement:
--   Let $n,\bar v,c>0$, $0<\beta\le1/2$, $0<q<1$, $0<\alpha<1$, $\lambda\ge1$ and $v'\ge0$ be the published model parameters. Put $z=1+(\lambda(1-q)/q)^{1/\alpha}$. Coverage uses the weak comparison of payer objectives, and equilibrium means a maximum of realized firm profit over all $p\ge0$. Assume Assumption 1, $\beta c/\bar v<\min\{q,1/z\}$.
--
--   Let $q_1,q_2\in(0,1)$ solve $z(q_1)q_1=2/\beta$ and $z(q_2)q_2=2/(1+\beta)$. There is a unique $\bar q_1\in(0,1)$ solving $z(\bar q_1)\bar q_1=1/\beta$, with $q_1<\bar q_1<q_2$. Set
--
--   $$a=1/q-z\beta/2,\quad b=1/q-z(1+\beta)/2,\quad p_1=\frac{q(v'+\bar v/2)}{1-qz\beta/2},\quad p_2=\frac{qv'}{1-qz(1+\beta)/2},$$
--   $$p^*=c/2+\bar v/(2\beta z),\qquad\bar p^*=c/2+\bar v/(2z).$$
--
--   Whenever $c\le\bar v/z$, there is a unique $p_3\in[c,\bar p^*]$ satisfying $\Pi^U_{firm}(\bar p^*;1)=\Pi^U_{firm}(p_3;\beta)$. All five assertions hold:
--
--   1. If $q\le\bar q_1$, or $q>\bar q_1$ and $v'\ge p^*a-\bar v/2$, then $p^*$ is the unique equilibrium price and is covered.
--   2. If $q>\bar q_1$ and $\max\{c,\bar v/z\}a-\bar v/2<v'<p^*a-\bar v/2$, then $p_1$ is the unique equilibrium price and is covered.
--   3. If $q>q_2$, $c\le\bar v/z$ and $p_3b\le v'\le(\bar v/z)b$, then $p_2$ is an equilibrium price and is covered; it is unique if $v'>p_3b$.
--   4. If $q>q_2$, $c\le\bar v/z$ and $v'<p_3b$, then $\bar p^*$ is an equilibrium price without coverage; it is unique if $c<\bar v/z$.
--   5. If $q>\bar q_1$, $c>\bar v/z$ and $v'\le(c/q)(1-qz\beta/2)-\bar v/2$, then realized profit is at most zero at every nonnegative price and attains zero. Coverage is absent on $(c,\bar v/(\beta z))$, and at $c$ too if the benefit inequality is strict.
--
--   The five cases are exhaustive provided $\neg(q=q_2\ \land\ v'=0\ \land\ c\le\bar v/z)$. Only this exhaustiveness clause has the extra premise; none of the five implications does. This supplies all regions of the uniform-pricing theorem, including both implicit-root clauses.
--
--   Differences from the source:
--   - encoding: the source model and its implicit nonnegative payer benefit → the published Params.Standing, including c > 0 and vp ≥ 0; reason: these are inherited disclosed base conventions; the proof on p. 54 uses vp ≥ 0; zero-cost games are excluded by the published interface; in Appendix F vp is unused and may always be set to zero
--   - reading: the firm prices at X → X is an equilibrium, the coverage decision at X is stated, and uniqueness is conditional at exact profit ties and zero margins; reason: the proof compares covered and uncovered profits; equal profits give multiple maximizing prices, so no uniqueness is claimed at those ties
--   - reading: makes no profit regardless of price and no coverage → realized profit ≤ 0 at every p ≥ 0, with zero attained; no coverage on the stated interval above cost and below the covered demand cutoff, and at cost when the benefit inequality is strict; reason: prices below cost lose money and a zero-demand payer is indifferent and covers; the proof of Theorem 1, pp. 52–53, restricts attention to the nonnegative-margin demand interval
--   - correction: the five cases are exhaustive → only the exhaustiveness clause additionally assumes ¬(q = q2 ∧ vp = 0 ∧ c ≤ vbar/z); reason: the exact rational counterexample in DISPROOF.md satisfies the standing assumptions and Assumption 1 but none of the printed cases; the final proof step on p. 54 incorrectly uses a strict inequality at q = q2
--   - reading: roots are given on [0,1] and on the implicit-price intervals → qbar1 is an existing unique root on (0,1), ordered between q1 and q2; p3 exists uniquely only if c ≤ vbar/z; reason: zOf at zero is undefined in the source, and the price-root interval is empty at high costs; all five case implications retain their source domains
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 16 (PDF 17), Theorem 1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_UniformPrices

namespace OutcomeRebate.Transfer.Supplement

/-- All five price regions; the printed exhaustiveness assertion is corrected only on its
missing boundary. Implicit price roots are required only in the applicable branches. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (hA : Assumption1 P) (q1 q2 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β)
    (hq2 : 0 < q2 ∧ q2 < 1 ∧ zOf P.α P.lam q2 * q2 = 2 / (1 + P.β)) :
    let rootQ := fun qb : ℝ => 0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb * qb = 1 / P.β
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc P.c (pBarStar P) ∧
      firmProfitU P 1 (pBarStar P) = firmProfitU P P.β p3
    let a := 1 / P.q - P.z * P.β / 2
    let b := 1 / P.q - P.z * (1 + P.β) / 2
    let p1 := P.q * (P.vp + P.vbar / 2) / (1 - P.q * P.z * P.β / 2)
    let p2 := P.q * P.vp / (1 - P.q * P.z * (1 + P.β) / 2)
    let C1 := fun qb => P.q ≤ qb ∨ (qb < P.q ∧ pStar P * a - P.vbar / 2 ≤ P.vp)
    let C2 := fun qb => qb < P.q ∧ max P.c (P.vbar / P.z) * a - P.vbar / 2 < P.vp ∧
      P.vp < pStar P * a - P.vbar / 2
    let C3 := fun p3 => q2 < P.q ∧ P.c ≤ P.vbar / P.z ∧ p3 * b ≤ P.vp ∧ P.vp ≤ P.vbar / P.z * b
    let C4 := fun p3 => q2 < P.q ∧ P.c ≤ P.vbar / P.z ∧ P.vp < p3 * b
    let C5 := fun qb => qb < P.q ∧ P.vbar / P.z < P.c ∧ P.vp ≤ P.c / P.q * (1 - P.q * P.z * P.β / 2) - P.vbar / 2
    (∃! qb, rootQ qb) ∧
    (P.c ≤ P.vbar / P.z → ∃! p3, rootP p3) ∧
    (∀ qb, rootQ qb → (q1 < qb ∧ qb < q2) ∧
      (C1 qb → IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧
        ∀ p, IsEqPriceU P p → p = pStar P) ∧
      (C2 qb → IsEqPriceU P p1 ∧ coversU P p1 ∧ ∀ p, IsEqPriceU P p → p = p1) ∧
      (∀ p3, rootP p3 →
        (C3 p3 → IsEqPriceU P p2 ∧ coversU P p2 ∧
          (p3 * b < P.vp → ∀ p, IsEqPriceU P p → p = p2)) ∧
        (C4 p3 → IsEqPriceU P (pBarStar P) ∧ ¬coversU P (pBarStar P) ∧
          (P.c < P.vbar / P.z → ∀ p, IsEqPriceU P p → p = pBarStar P))) ∧
      (C5 qb → (∀ p, 0 ≤ p → realizedProfitU P p ≤ 0) ∧
        (∃ p, 0 ≤ p ∧ realizedProfitU P p = 0) ∧
        (∀ p, P.c < p → p < P.vbar / (P.β * P.z) → ¬coversU P p) ∧
        (P.vp < P.c / P.q * (1 - P.q * P.z * P.β / 2) - P.vbar / 2 → ¬coversU P P.c)) ∧
      (¬(P.q = q2 ∧ P.vp = 0 ∧ P.c ≤ P.vbar / P.z) →
        C1 qb ∨ C2 qb ∨ (∃ p3, rootP p3 ∧ C3 p3) ∨ (∃ p3, rootP p3 ∧ C4 p3) ∨ C5 qb)) := by sorry

end OutcomeRebate.Transfer.Supplement
