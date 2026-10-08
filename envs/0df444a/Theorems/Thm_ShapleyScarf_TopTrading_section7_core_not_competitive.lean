-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_section7_core_not_competitive
-- name    : ShapleyScarf.TopTrading.section7_core_not_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:05.169964+00:00
-- url     : https://prove2.me/theorems/f0e3e190-8be3-4099-97ea-dbe97ea0c734
-- title:
--   Section 7, pp. 115-116 — a core allocation that is not competitive
-- statement:
--   Consider the market with three traders $1,2,3$ and preference matrix (rows are traders, columns are goods)
--   $$A = \begin{pmatrix} 0 & 1 & 2\\ 1 & 0 & -1\\ -1 & 1 & 0\end{pmatrix}.$$
--   Then:
--
--   1. the only competitive allocation is the one given by the $N$-permutation $\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}$ (trader 1 gets good 3, trader 2 gets good 1, trader 3 gets good 2): it is competitive when all prices are equal, every allocation that is competitive at some prices gives the payoff $(2,1,1)$, and the competitive prices are all equal;
--   2. the allocation of the $N$-permutation $\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}$ (traders 1 and 2 swap, trader 3 keeps his good), with payoff $(1,1,0)$, is a core allocation;
--   3. that allocation is competitive at no price vector.
--
--   The example answers the question whether every core allocation of such a market is competitive: the core is strictly larger than the set of competitive allocations.
--
--   **Formalization Note** Traders and goods $1,2,3$ are `0, 1, 2 : Fin 3`; the matrix is `![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]]` and the swap allocation is the map `![1, 0, 2]`. Competitive and core allocations are those of the definition item `ShapleyScarf.TopTrading.Market`; item 3 is stated for all real price vectors, not only positive ones. Item 1 (existence at equal prices, then uniqueness of the payoff and equality of the prices) makes explicit the page's "the competitive prices are all equal and the unique competitive payoff is (2, 1, 1)".
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); pp. 115-116 of the source printing, Section 7

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market

namespace ShapleyScarf.TopTrading

/-- §7, pp. 115–116: in the three-trader market with preference matrix
`(0 1 2 / 1 0 −1 / −1 1 0)` (traders `1, 2, 3` = `0, 1, 2`), the allocation of the
`N`-permutation `(0 0 1 / 1 0 0 / 0 1 0)` is competitive at equal prices, every competitive
allocation gives the payoff `(2, 1, 1)` at equal prices, while the allocation of the `N`-permutation
`(0 1 0 / 1 0 0 / 0 0 1)` (payoff `(1, 1, 0)`) is a core allocation that is competitive at no
price vector. -/
theorem section7_core_not_competitive :
    IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![2, 0, 1]
        (fun _ => 1) ∧
    (∀ (σ : Fin 3 → Fin 3) (price : Fin 3 → ℝ),
        IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) σ price →
          (fun i => (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) i (σ i))
              = ![2, 1, 1] ∧
            ∀ k k', price k = price k') ∧
      IsCoreAllocation (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![1, 0, 2] ∧
      ¬ ∃ price : Fin 3 → ℝ,
          IsCompetitive (![![0, 1, 2], ![1, 0, -1], ![-1, 1, 0]] : Fin 3 → Fin 3 → ℝ) ![1, 0, 2]
            price := by sorry

end ShapleyScarf.TopTrading
