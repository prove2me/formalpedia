-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_packing_array_exec
-- name    : PandoraKnapsack.Skipping.ArrayRAM.packing_array_exec
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:48:20.076342+00:00
-- url     : https://prove2.me/theorems/61049eed-f652-4a1d-917d-38bbf9790f1d
-- title:
--   Polynomial-time execution of the normalized packing solver
-- statement:
--   For every row count $r$, column count $d$ and real matrix and profit vector in the designated input tables, the imperative packing block writes the vector computed by the bounded projected-row algorithm to its answer table. There is a fixed exponent $e$ with execution cost at most $(r+d+2)^e$. The dimensions, previously computed time labels and rewards needed for sampling are preserved, as is the draw count.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and Theorem 5.1, Appendix B.1; original machine-implementation lemma for the stated Prove2Me exact coefficient-access model.

import Definitions.Def_PandoraKnapsack_Skipping_PackingRAM
import Definitions.Def_PandoraKnapsack_NormalizedPacking

namespace PandoraKnapsack.Skipping.ArrayRAM

theorem packing_array_exec :
    ∃ e : ℕ, ∀ {r d n m T : ℕ} (I : Instance n m T) (ω : ℕ → ℝ) (s : Store)
      (A : PandoraPacking.Matrix r d) (c : PandoraPacking.Vec d),
      s.ns 3 = d → s.ns 4 = r →
      (∀ i : Fin r, ∀ j : Fin d, s.tab 2 (i.val * d + j.val) = A i j) →
      (∀ j : Fin d, s.tab 3 j.val = c j) →
      ∃ v k, Exec I ω packingCode s v k ∧ k ≤ (r+d+2)^e ∧
        (∀ j : Fin d, v.tab 4 j.val = PandoraPacking.solve A c j) ∧
        (∀ j < 25, v.ns j = s.ns j) ∧ (∀ j < 25, v.rs j = s.rs j) ∧
        (∀ t : Fin 16, t ≠ 4 → t ≠ 5 → v.tab t = s.tab t) ∧
        v.out = s.out ∧ v.draws = s.draws := by sorry

end PandoraKnapsack.Skipping.ArrayRAM
