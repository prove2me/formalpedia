-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_block_decomposition
-- name    : SwitchbackExp.CLT.block_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:02.921047+00:00
-- url     : https://prove2.me/theorems/0fc5dc00-f576-4111-9c75-f05694c642b4
-- title:
--   EC.4.1–EC.4.2, p. ec25 — τ̂_m − τ_m = (T − m)⁻¹ ∑_{k=0}^{n−2} 𝟙̄_k and each 𝟙̄_k has mean zero
-- statement:
--   Let $m\ge1$, $n\ge4$, $T=nm$, and let the potential outcomes satisfy Assumptions 1 (non-anticipation) and 2 ($m$-carryover). Consider the optimal design $\mathbb T^*=\{1,2m+1,\dots,(n-2)m+1\}$ with fair coins, and the block errors $\bar{\mathbb 1}_0,\dots,\bar{\mathbb 1}_{n-2}$ of EC.4.1. Then:
--
--   1. On every assignment path the design can produce,
--   $$\hat\tau_m-\tau_m=\frac1{T-m}\sum_{k=0}^{n-2}\bar{\mathbb 1}_k .$$
--   2. Each block error has mean zero: $\mathbb E[\bar{\mathbb 1}_k]=0$ for $k=0,1,\dots,n-2$.
--
--   The decomposition turns the estimation error into a sum of $n-1$ centred block terms, each depending on at most two neighbouring coin flips; it is the starting point of the variance formula (Lemma 2) and of the central limit theorem (Theorem 3).
--
--   **Formalization Note** The paper writes the upper index as $K+1$ with $K=n-3$. A path the design can produce is the image of a coin vector under the path map; the expectation is over the fair coins.
-- source:
--   arXiv:2009.00148v4, EC.4.1, p. ec25 (display after Table EC.7) and EC.4.2, proof of Lemma 2, p. ec25 (first sentence)

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_CLT_Setting

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

/-- EC.4.1–EC.4.2, p. ec25: under the optimal design with `T = n m`, `n ≥ 4`, and Assumptions 1–2,
`τ̂_m − τ_m = (1/(T − m)) ∑_{k=0}^{n−2} 𝟙̄_k` on every realized path, and each block error `𝟙̄_k` has
mean zero. -/
theorem block_decomposition (m n : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (Y : Outcomes)
    (hA1 : NonAnticipating (n * m) Y) (hA2 : Carryover m (n * m) Y) :
    (∀ c : Coins m n,
      htEstimator m (n * m) (optPoints m n) half Y (pathOf (optPoints m n) c) - tau m (n * m) Y
        = 1 / (((n * m : ℕ) : ℝ) - m) *
            ∑ k ∈ Finset.range (n - 1), blockErr m (optPoints m n) half Y k (pathOf (optPoints m n) c)) ∧
    (∀ k < n - 1, expect (optPoints m n) half (blockErr m (optPoints m n) half Y k) = 0) := by sorry

end SwitchbackExp.CLT
