-- Prove2me | Theorems.Thm_SupplyChainTheory_echelon_local_holding
-- name    : SupplyChainTheory.echelon_local_holding
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:16:46.798124+00:00
-- url     : https://prove2.me/theorems/9138e353-4fd8-4e06-a5e7-a979f6b66862
-- title:
--   Proposition 6.1: $\sum_j h_j I_j = \sum_j h'_j (I'_j + IT_{j-1})$, echelon and local holding costs agree
-- statement:
--   **Proposition 6.1.** In an $N$-stage serial system with local holding costs $h'_j$, echelon
--   holding costs $h_j = h'_j - h'_{j+1}$ ($h'_{N+1} = 0$), local on-hand inventories $I'_j$,
--   in-transit inventories $IT_{j-1}$ ($IT_0 = 0$) and echelon on-hand inventories
--   $I_j = \sum_{i=1}^j (I'_i + IT_{i-1})$,
--
--   $$ \sum_{j=1}^N h_j I_j \;=\; \sum_{j=1}^N h'_j\,(I'_j + IT_{j-1}). $$
--
--   Total holding cost can be computed with either echelon or local quantities. The book omits
--   the proof (Problem 6.4); it is a summation by parts. This is what allows the chapter to
--   optimize echelon base-stock levels with the echelon cost (6.9) in place of the local cost
--   (6.8).
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 192, Sect. 6.2.1, Proposition 6.1, Eq. (6.5): 'Proof. Omitted; see Problem 6.4'

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem echelon_local_holding (N : ℕ) (h' I' IT : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 N, echelonHolding N h' j * echelonOnHand I' IT j
      = ∑ j ∈ Finset.Icc 1 N, h' j * (I' j + if j = 1 then 0 else IT (j - 1)) := by sorry

end SupplyChainTheory
