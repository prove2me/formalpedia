-- Prove2me | Theorems.Thm_SeqLoss_Equidistance_theorem_2
-- name    : SeqLoss.Equidistance.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:40.113923+00:00
-- url     : https://prove2.me/theorems/4cd49405-1f6e-41bc-8a4c-f64fd7416109
-- title:
--   Theorem 2 — for equal losses the midpoint rule $\varphi^{1/2}(\ell)$ is at equal Euclidean distance from $c_1,\dots,c_n$
-- statement:
--   Let $n\ge 1$ and let $\ell\in L^n$ be a loss problem with equal losses, $\ell_1=\dots=\ell_n$, and total $L$. Let $c_k=(L/k,\dots,L/k,0,\dots,0)$, with $k$ entries $L/k$, be the ideal allocations, $k=1,\dots,n$. Then the midpoint fixed-fraction allocation
--   $$\varphi^{1/2}(\ell)=\Big(\frac{\ell_1}{2}+\frac L2,\ \frac{\ell_2}{2},\dots,\frac{\ell_n}{2}\Big)$$
--   is at equal Euclidean distance from all of them:
--   $$d\big(\varphi^{1/2}(\ell),c_k\big)=d\big(\varphi^{1/2}(\ell),c_{k'}\big)\qquad\text{for all }k,k'\in\{1,\dots,n\}.$$
--
--   Each $c_k$ is the allocation most favourable to agent $k+1$ (and $c_n$ to agent $1$) among the ordered allocations, so the theorem says that the midpoint rule treats all agents' ideal outcomes alike, which is the paper's first normative argument for $\lambda=1/2$.
--
--   **Formalization Note** The paper's $\mathbb N$ starts at $1$, hence $n\ge 1$. Distances are Euclidean (Mathlib's `EuclideanSpace ℝ (Fin n)`), not the sup distance on `Fin n → ℝ`.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 14, Theorem 2

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_Equidistance_IdealAllocations

namespace SeqLoss.Equidistance
theorem theorem_2 (n : ℕ) (hn : 0 < n) (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ)
    (heq : ∀ i j, ℓ i = ℓ j) :
    ∀ k k' : ℕ, 1 ≤ k → k ≤ n → 1 ≤ k' → k' ≤ n →
      euclDist (SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) (ideal ℓ k) =
        euclDist (SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) (ideal ℓ k') := by sorry
end SeqLoss.Equidistance
