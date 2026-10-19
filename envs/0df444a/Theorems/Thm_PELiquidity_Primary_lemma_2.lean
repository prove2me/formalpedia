-- Prove2me | Theorems.Thm_PELiquidity_Primary_lemma_2
-- name    : PELiquidity.Primary.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:06.988653+00:00
-- url     : https://prove2.me/theorems/885c4847-e762-499b-a17a-ff564d7774a4
-- title:
--   Lemma 2, p. 18 — the minimal expected IC fee is (15), and x ∈ [q/(p+q), p/(p+q)] minimizes it
-- statement:
--   Let $0<q<p\le 1$, $B>0$ and $B\le p(p-q)R$. For a share $x\in[0,1]$ of the fund invested in period 0, consider the fee schedules $f$ satisfying limited liability (2) and incentive compatibility (effort on both investments). The minimal expected fee $\bar f$ over these schedules is
--
--   $$\bar f^*_x=\begin{cases}\dfrac{pB}{p-q}(1-x) & x\in\big[0,\tfrac{q}{p+q}\big],\\[2mm] \dfrac{p^2B}{p^2-q^2} & x\in\big[\tfrac{q}{p+q},\tfrac{p}{p+q}\big],\\[2mm] \dfrac{pB}{p-q}\,x & x\in\big[\tfrac{p}{p+q},1\big],\end{cases}\qquad(15)$$
--
--   and the minimum is attained. Moreover, a share $x\in[0,1]$ belongs to a pair $(x,f)$ minimizing the expected fee over all $x'\in[0,1]$ and all admissible schedules if and only if
--   $$x\in\Big[\frac{q}{p+q},\frac{p}{p+q}\Big].$$
--
--   The minimal fee is U-shaped in $x$: spreading the fund over two investments lets the GP be paid only after a joint success, which is the most informative outcome about effort (cross-pledging).
--
--   **Formalization Note** The hypothesis $B\le p(p-q)R$ guarantees that the incentive-compatible fee paid on joint success never exceeds the cash flow $R$, so that limited liability can be met at every $x$. Fees are indexed by the four outcomes.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 17–18, Lemma 2, (13)–(15)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- Lemma 2: the minimal expected fee over limited-liability, incentive-compatible fee
schedules, for a first call `x ∈ [0, 1]`, is (15); and the call fractions `x` that are
part of an unconstrained fee-minimizing pair `(x, f)` are exactly `[q/(p+q), p/(p+q)]`. -/
theorem lemma_2 (p q B R : ℝ) (hq : 0 < q) (hqp : q < p) (hp1 : p ≤ 1) (hB : 0 < B)
    (hLL : B ≤ p * (p - q) * R) :
    (∀ x : ℝ, 0 ≤ x → x ≤ xLow p q →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p * B / (p - q) * (1 - x))) ∧
    (∀ x : ℝ, xLow p q ≤ x → x ≤ xBar p q →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p ^ 2 * B / (p ^ 2 - q ^ 2))) ∧
    (∀ x : ℝ, xBar p q ≤ x → x ≤ 1 →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p * B / (p - q) * x)) ∧
    (∀ x : ℝ, (0 ≤ x ∧ x ≤ 1 ∧ ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
        ∀ (x' : ℝ) (f' : Outcome → ℝ), 0 ≤ x' → x' ≤ 1 → IsLimitedLiability R x' f' →
          IsIC p q B x' f' → expectedFee p p f ≤ expectedFee p p f') ↔
      x ∈ Set.Icc (xLow p q) (xBar p q)) := by sorry

end PELiquidity.Primary
