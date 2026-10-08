-- Prove2me | Theorems.Thm_ShapleyScarf_Balanced_doublyStochastic_balancingCombination
-- name    : ShapleyScarf.Balanced.doublyStochastic_balancingCombination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:22.195551+00:00
-- url     : https://prove2.me/theorems/aea19266-bb40-43dc-8082-fd7a2547b811
-- title:
--   Section 4 — balanced permutation mixtures are doubly stochastic
-- statement:
--   Let $T$ be a balanced family with balancing weights $\delta_S$, and choose an $S$-permutation matrix $P_S$ for every $S\in T$. Then
--   $$
--   D=\sum_{S\in T}\delta_S P_S
--   $$
--   has nonnegative entries and every row and column sums to 1; equivalently, $D$ is doubly stochastic.
--
--   The result identifies the matrix produced by balancing the coalition allocations with the standard doubly stochastic matrix class.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; p. 110 of the source printing, Section 4, proof of the Theorem, paragraph beginning 'The crucial fact about D'

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem doublyStochastic_balancingCombination {N : Type*} [Fintype N] [DecidableEq N]
    [Nonempty N] (T : Finset (Finset N)) (δ : Finset N → ℝ)
    (P : Finset N → Matrix N N ℝ)
    (hT : IsBalancedFamily T) (hδ : IsBalancingWeights T δ)
    (hP : ∀ S ∈ T, IsSPermutation S (P S)) :
    (∑ S ∈ T, δ S • P S) ∈ doublyStochastic ℝ N := by sorry

end ShapleyScarf.Balanced
