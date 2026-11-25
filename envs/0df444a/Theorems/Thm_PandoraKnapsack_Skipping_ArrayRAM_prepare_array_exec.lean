-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_prepare_array_exec
-- name    : PandoraKnapsack.Skipping.ArrayRAM.prepare_array_exec
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:49:31.271026+00:00
-- url     : https://prove2.me/theorems/ded81336-1a74-4e62-b660-42ac85833235
-- title:
--   Polynomial-time assembly of dyadic packing inputs
-- statement:
--   On every instance, the preprocessing block materializes the dyadic grid, raw effective rewards, normalized packing matrix and normalized profit vector in their designated arrays. All dimensions are correct and no draws have been used. A single exponent $e$ bounds its charged execution cost by $(n+m+\mathrm{bitlength}(T)+2)^e$.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and Theorem 5.1, Appendix B.1; original machine-implementation lemma for the stated Prove2Me exact coefficient-access model.

import Definitions.Def_PandoraKnapsack_Skipping_PrepareRAM
import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan

namespace PandoraKnapsack.Skipping.ArrayRAM

/-- A fixed preprocessing program builds dyadic start times, objective weights, and
the normalized packing LP in polynomial time without consuming a random draw. -/
theorem prepare_array_exec : ∃ e : ℕ, ∀ (n m T : ℕ) (I : Instance n m T) (ω : ℕ → ℝ),
    ∃ (v : Store) (k : ℕ), Exec I ω Prepare.code (initial n m T) v k ∧
      k ≤ (inputSize n m T + 2)^e ∧ v.ns 0 = n ∧ v.ns 1 = m ∧
      v.ns 2 = labelCount T ∧ v.ns 3 = columnCount n m T ∧ v.ns 4 = timeRows n T ∧
      v.rs 0 = T ∧ (∀ h : Fin (labelCount T), v.tab 0 h.val = timeLabel h) ∧
      (∀ col : Fin (columnCount n m T), v.tab 1 col.val = columnWeight I col) ∧
      (∀ row : Fin (timeRows n T), ∀ col : Fin (columnCount n m T),
        v.tab 2 (row.val*columnCount n m T+col.val) = packingRows I row col) ∧
      (∀ col : Fin (columnCount n m T), v.tab 3 col.val = packingProfits I col) ∧ v.draws = 0 := by sorry

end PandoraKnapsack.Skipping.ArrayRAM
