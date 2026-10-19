-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_eq_A_25
-- name    : SmartExpedite.PolicyM.eq_A_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:29.774303+00:00
-- url     : https://prove2.me/theorems/10bad11c-bb9b-45a9-b46d-02afee1347e5
-- title:
--   (A-25), p. 36 — indicator partition for a nonempty receiving node
-- statement:
--   Let $K\ge1$ and let $u$ be Policy-M parameters satisfying Assumption A. Fix a node $i$ with $2\le i\le K$ and an admissible state $n\in S_M(u)$. With $A_m,D_m,E_i,F_i$ as in (A-16) and (A-19)–(A-21),
--
--   $$\sum_{m=1}^{i-2}\mathbf1_{A_m\cap D_m}(n)+\mathbf1_{E_i}(n)+\mathbf1_{F_i}(n)=\mathbf1_{\{n_i>0\}}(n).$$
--
--   This indicator identity is the combinatorial step that reduces the paper's local balance equations to occupancy conditions.
--
--   **Formalization Note** The case $i=K$ is used on p. 38 for (A-15); an empty sum is zero.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), p. 36, (A-25); p. 38, use at i = K

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

attribute [local instance] Classical.propDecidable

/-- Equation (A-25), p. 36: the indicators partition the states with an item
at node `i`. The case `i = K` is used for (A-15) on p. 38. -/
theorem eq_A_25 (K : ℕ) (u : ℕ → ℕ → ℕ∞)
    (hK : 1 ≤ K) (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    ∀ i, 2 ≤ i → i ≤ K → ∀ n ∈ SM K u,
      (∑ m ∈ Finset.Icc 1 (i - 2),
          (if n ∈ Aset K u i m ∩ Dset K u i m then 1 else 0 : ℕ)) +
        (if n ∈ Eiset K u i then 1 else 0) +
        (if n ∈ Fset K u i then 1 else 0) =
        (if 0 < occ n i then 1 else 0) := by sorry

end SmartExpedite.PolicyM
