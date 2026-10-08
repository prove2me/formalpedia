-- Prove2me | Theorems.Thm_RetailVariety_Statics_eq_14
-- name    : RetailVariety.Statics.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:40.105219+00:00
-- url     : https://prove2.me/theorems/fa46f089-a6b8-404a-90fe-7a07c7c4355a
-- title:
--   (14): $\pi_T(A_{i+1})\ge\pi_T(A_i)$ iff $\sum_{j\le i+1}(pw_j-c)^+\ge\sum_{j\le i}(pt_j-c)^+$
-- statement:
--   Let $i<n$, preferences $v_1,\dots,v_n$, no-purchase preference $v_0$, price $p$, cost $c$, and store volume $\lambda>0$. With $t_j$ and $w_j$ the multinomial logit shares on $A_i$ and $A_{i+1}$,
--   $$t_j=\frac{v_j}{\sum_{k=1}^{i}v_k+v_0},\qquad w_j=\frac{v_j}{\sum_{k=1}^{i+1}v_k+v_0},$$
--   the trend-following profits compare as
--   $$\pi_T(A_{i+1},v)\ge\pi_T(A_i,v)\iff\sum_{j=1}^{i+1}(pw_j-c)^+\ge\sum_{j=1}^{i}(pt_j-c)^+,\tag{14}$$
--   and the same equivalence holds with both inequalities strict.
--
--   This removes the volume $\lambda$ from the comparison in the trend-following model, which is why no volume effect (part (c) of Theorem 2) exists there.
--
--   **Formalization Note** The paper prints only the forward implication of the non-strict version; since $\lambda>0$ is a common factor, both directions and the strict version hold and are stated. Variants are 0-indexed in Lean.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, eq. (14)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem eq_14 (n i : ℕ) (hin : i < n) (v : Fin n → ℝ) (v0 p c lam : ℝ) (hlam : 0 < lam) :
    (RetailVariety.Structure.profitT p c lam v v0 (A n i) ≤ RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) ↔
      ∑ j ∈ A n i, max (p * RetailVariety.Structure.share v v0 (A n i) j - c) 0
        ≤ ∑ j ∈ A n (i + 1), max (p * RetailVariety.Structure.share v v0 (A n (i + 1)) j - c) 0) ∧
    (RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) ↔
      ∑ j ∈ A n i, max (p * RetailVariety.Structure.share v v0 (A n i) j - c) 0
        < ∑ j ∈ A n (i + 1), max (p * RetailVariety.Structure.share v v0 (A n (i + 1)) j - c) 0) := by sorry

end RetailVariety.Statics
