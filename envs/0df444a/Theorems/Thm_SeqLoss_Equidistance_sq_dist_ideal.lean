-- Prove2me | Theorems.Thm_SeqLoss_Equidistance_sq_dist_ideal
-- name    : SeqLoss.Equidistance.sq_dist_ideal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:11.891913+00:00
-- url     : https://prove2.me/theorems/5425d35a-74a2-4c2d-962c-45da1e1a295a
-- title:
--   Proof of Theorem 2, p. 23 — squared Euclidean distance from $x$ to the ideal allocation $c_k$
-- statement:
--   Let $\ell\in\mathbb R^n$ have total $L=\ell_1+\dots+\ell_n$, let $1\le k\le n$, and let $c_k=(L/k,\dots,L/k,0,\dots,0)$ be the $k$-th ideal allocation. For every $x\in\mathbb R^n$,
--   $$d(x,c_k)^2=\sum_{i=1}^k\Big(x_i-\frac Lk\Big)^2+\sum_{i=k+1}^n x_i^2=\sum_{i=1}^n x_i^2-\frac{2L}{k}\sum_{i=1}^k x_i+\frac{L^2}{k}.$$
--
--   The first term does not depend on $k$, so equidistance from $c_1,\dots,c_n$ reduces to the last two terms being independent of $k$.
--
--   **Formalization Note** The paper writes the identity for $x\in\bar X(\ell)$; it holds for every real vector $x$ and every real $\ell$, and is stated so. Agents are 0-based, so $\sum_{i=1}^k x_i$ is the sum over indices $i<k$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 23, Appendix A, proof of Theorem 2, first display

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_Equidistance_IdealAllocations

namespace SeqLoss.Equidistance
theorem sq_dist_ideal {n : ℕ} (ℓ x : Fin n → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    euclDist x (ideal ℓ k) ^ 2 =
      (∑ i, x i ^ 2)
        - 2 * SeqLoss.FixedFraction.total ℓ / (k : ℝ) * (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i)
        + SeqLoss.FixedFraction.total ℓ ^ 2 / (k : ℝ) := by sorry
end SeqLoss.Equidistance
