-- Prove2me | Theorems.Thm_RetailVariety_Statics_numerator13_tendsto_pos
-- name    : RetailVariety.Statics.numerator13_tendsto_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:03.516225+00:00
-- url     : https://prove2.me/theorems/609c711a-297d-4db9-a3e7-d28e607a66a9
-- title:
--   The numerator of (13) tends to a positive constant as $v_0\to0$
-- statement:
--   Let $n>i\ge1$, $v_1\ge v_2\ge\dots\ge v_n>0$ and $0\le\beta<1$. Write $V_k=\sum_{j=1}^{k}v_j$. As the no-purchase preference $v_0$ decreases to $0$ through positive values, the numerator of the right side of (13) converges:
--   $$\sum_{j=1}^{i+1}w_j^\beta-\sum_{j=1}^{i}t_j^\beta\ \longrightarrow\ \sum_{j=1}^{i+1}\Big(\frac{v_j}{V_{i+1}}\Big)^{\beta}-\sum_{j=1}^{i}\Big(\frac{v_j}{V_i}\Big)^{\beta},$$
--   where $t_j$, $w_j$ are the multinomial logit shares on $A_i$, $A_{i+1}$; and this limit is strictly positive.
--
--   Together with the vanishing denominator, this makes the right side of (13) tend to $+\infty$ as $v_0\to0$, which is the content of part (b) of Theorem 2 for the independent model.
--
--   **Formalization Note** The paper asserts this ("one can easily show the numerators tend to a positive constant") without proof. The decreasing order of the preferences is needed for positivity. Variants are 0-indexed in Lean; powers are real powers.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, part (b)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem numerator13_tendsto_pos (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ)
    (hv : ∀ j, 0 < v j) (hanti : Antitone v) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun v0 : ℝ => ∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β
          - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β) (𝓝[>] 0)
        (𝓝 (∑ j ∈ A n (i + 1), (v j / ∑ k ∈ A n (i + 1), v k) ^ β
          - ∑ j ∈ A n i, (v j / ∑ k ∈ A n i, v k) ^ β)) ∧
      0 < ∑ j ∈ A n (i + 1), (v j / ∑ k ∈ A n (i + 1), v k) ^ β
          - ∑ j ∈ A n i, (v j / ∑ k ∈ A n i, v k) ^ β := by sorry

end RetailVariety.Statics
