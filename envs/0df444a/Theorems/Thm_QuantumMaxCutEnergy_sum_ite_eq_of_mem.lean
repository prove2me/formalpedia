-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_sum_ite_eq_of_mem
-- name    : QuantumMaxCutEnergy.sum_ite_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:32:58.257114+00:00
-- url     : https://prove2.me/theorems/79c93bec-5634-4a51-a73a-62f9e75c7630
-- title:
--   Summing a single-coordinate indicator over a finite vertex set
-- statement:
--   **Summing a single-coordinate indicator.**
--
--   For a finite set of vertices $S$, a vertex $a$ and a constant $c$,
--   $$\sum_{v\in S}\begin{cases}c,&v=a\\ 0,&v\ne a\end{cases}=\begin{cases}c,&a\in S\\0,&a\notin S.\end{cases}$$
--
--   **Role.** Pure bookkeeping, used to split a sum of loads into its two endpoint contributions when converting
--   load masses into internal edge masses.
--
--   *Formalization note.* The statement is about `Finset` sums over `Fin n`.
-- source:
--   Elementary finite-sum bookkeeping used in the odd-set/uncrossing analysis of Edmonds' matching polytope (J. Res. Nat. Bur. Standards 69B, 1965).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- Summing a single-coordinate indicator over a finite set. -/
theorem sum_ite_eq_of_mem {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (c : ℝ) :
    ∑ v ∈ S, (if v = a then c else 0) = if a ∈ S then c else 0 := by sorry

end QuantumMaxCutEnergy
