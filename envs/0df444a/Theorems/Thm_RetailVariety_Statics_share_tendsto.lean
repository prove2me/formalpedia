-- Prove2me | Theorems.Thm_RetailVariety_Statics_share_tendsto
-- name    : RetailVariety.Statics.share_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:56.284819+00:00
-- url     : https://prove2.me/theorems/c5a63690-a075-467d-8b68-3a233252aad5
-- title:
--   Shares as $v_0\to0$: $q_j\to v_j/\sum_{S}v_k$, hence $\sum w_j-\sum t_j\to 0$
-- statement:
--   Let $v_1,\dots,v_n>0$. As the no-purchase preference $v_0$ decreases to $0$ (through positive values):
--
--   1. for every nonempty assortment $S$ and every variant $j$,
--   $$q_j(S)=\frac{v_j}{\sum_{k\in S}v_k+v_0}\ \longrightarrow\ \frac{v_j}{\sum_{k\in S}v_k};$$
--   2. for every $1\le i<n$, with $t_j$, $w_j$ the shares on $A_i$, $A_{i+1}$,
--   $$\sum_{j=1}^{i+1}w_j-\sum_{j=1}^{i}t_j\ \longrightarrow\ 0 .$$
--
--   The second statement says that the denominator of the right side of (13) vanishes as $v_0\to0$; it is the first step of part (b) of Theorem 2.
--
--   **Formalization Note** The limit is taken along $v_0\to0^+$ (`𝓝[>] 0`), since $v_0>0$ throughout the model. Variants are 0-indexed in Lean.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1508, Appendix, Proof of Theorem 2, part (b)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem share_tendsto (n : ℕ) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) :
    (∀ (S : Finset (Fin n)) (j : Fin n), S.Nonempty →
      Tendsto (fun v0 : ℝ => RetailVariety.Structure.share v v0 S j) (𝓝[>] 0) (𝓝 (v j / ∑ k ∈ S, v k))) ∧
    (∀ i : ℕ, 1 ≤ i → i < n →
      Tendsto (fun v0 : ℝ => ∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j
          - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j) (𝓝[>] 0) (𝓝 0)) := by sorry

end RetailVariety.Statics
