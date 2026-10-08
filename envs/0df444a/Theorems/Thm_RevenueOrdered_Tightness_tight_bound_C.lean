-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tight_bound_C
-- name    : RevenueOrdered.Tightness.tight_bound_C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:50.154976+00:00
-- url     : https://prove2.me/theorems/8c20c7a3-a90a-4369-83df-44a6cb156d1f
-- title:
--   Theorem 3.4 proof, p. 11 — $N_i=\varepsilon^i+\dots+\varepsilon^k$ and $\sum_i (N_i-N_{i+1})/N_i\to k$
-- statement:
--   Let $k\ge1$, consider the tight instance, and define $N_i$ ($i\in[k]$) with respect to the optimal solution $S^*=\{(i,i): i\in[k]\}$, that is $N_i=\sum_{x\in S^*,\,r(x)\ge r_i}\mathcal P(x,S^*)$. Then:
--   1. for every $0<\varepsilon\le\tfrac12$ and $i\in[k]$, $N_i=\varepsilon^i+\dots+\varepsilon^k$;
--   2. as $\varepsilon\to0^+$,
--   $$
--   \sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\longrightarrow k ,
--   $$
--   where $N_{k+1}=0$ and $\ell$ is the largest index with $N_\ell>0$ (here $\ell=k$).
--
--   This shows that Theorem 3.3 is tight.
--
--   **Formalization Note** The sorted revenues are indexed from $0$: the Lean index $i$ is the paper's $i+1$, so part 1 reads $N_{i}=\sum_{j=i+1}^{k}\varepsilon^j$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 11, proof of Theorem 3.4

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance
open Filter Topology

namespace RevenueOrdered.Tightness

/-- Bound (C) is tight (p. 11): with `N_i` defined w.r.t. the optimal solution
`S^* = {(i, i) : i ∈ [k]}`, `N_i = ε^i + ⋯ + ε^k` for each `i ∈ [k]` (0-based index `i` here
stands for the paper's `i + 1`), and `∑_{i=1}^{ℓ} (N_i - N_{i+1}) / N_i` tends to `k` as `ε → 0⁺`. -/
theorem tight_bound_C (k : ℕ) [NeZero k] :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ i : Fin (numRevenues (tightRevenue k ε)),
        purchaseAbove (tightP k ε) (tightRevenue k ε) (diagonalSet k) i =
          ∑ j ∈ Finset.Icc (i.val + 1) k, ε ^ j) ∧
      Tendsto (fun ε : ℝ => purchaseGapSum (tightP k ε) (tightRevenue k ε) (diagonalSet k))
        (𝓝[>] 0) (𝓝 (k : ℝ)) := by sorry

end RevenueOrdered.Tightness
