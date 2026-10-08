-- Prove2me | Theorems.Thm_RetailVariety_Statics_eq_13
-- name    : RetailVariety.Statics.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:40.824229+00:00
-- url     : https://prove2.me/theorems/6a5d39ee-852a-4258-aa04-f7da9ca23237
-- title:
--   (13): $\pi_I(A_{i+1})\ge\pi_I(A_i)$ iff $(1-c/p)\frac{\sqrt{2\pi}}{\sigma}\lambda^{1-\beta}e^{z^2/2}\ge\frac{\sum w_j^\beta-\sum t_j^\beta}{\sum w_j-\sum t_j}$
-- statement:
--   Let $n>i\ge 1$, preferences $v_1,\dots,v_n>0$ and no-purchase preference $v_0>0$. Let $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$, and let $z=\Phi^{-1}(1-c/p)$. Write the multinomial logit shares on the two consecutive prefix sets as
--   $$t_j=\frac{v_j}{\sum_{k=1}^{i}v_k+v_0}\ (j\le i),\qquad w_j=\frac{v_j}{\sum_{k=1}^{i+1}v_k+v_0}\ (j\le i+1).$$
--   Then in the independent population model
--   $$\pi_I(A_{i+1},v)\ge\pi_I(A_i,v)\iff \left(1-\frac{c}{p}\right)\frac{\sqrt{2\pi}}{\sigma}\lambda^{1-\beta}e^{z^2/2}\ \ge\ \frac{\sum_{j=1}^{i+1}w_j^\beta-\sum_{j=1}^{i}t_j^\beta}{\sum_{j=1}^{i+1}w_j-\sum_{j=1}^{i}t_j},\tag{13}$$
--   and the same equivalence holds with both inequalities strict.
--
--   Inequality (13) separates the comparison of $A_{i+1}$ with $A_i$ into a left side that depends on $p$ and $\lambda$ but not on the shares, and a right side that depends on the shares but not on $p$ or $\lambda$. Every part of Theorem 2 for the independent model is read off from it.
--
--   **Formalization Note** The paper prints the non-strict equivalence; the strict one is the same computation and is what Theorem 2 uses, so both are stated. The denominator $\sum w_j-\sum t_j$ is positive because $v_{i+1}>0$ and $v_0>0$, so the quotient is an honest real quotient. Variants are 0-indexed in Lean.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, eq. (13)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem eq_13 (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (v0 : ℝ) (hv0 : 0 < v0) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) ≤ RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) ↔
      (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β)
          / (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j)
        ≤ (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
            * Real.exp (criticalFractile p c ^ 2 / 2)) ∧
    (RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) ↔
      (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β)
          / (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j)
        < (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
            * Real.exp (criticalFractile p c ^ 2 / 2)) := by sorry

end RetailVariety.Statics
