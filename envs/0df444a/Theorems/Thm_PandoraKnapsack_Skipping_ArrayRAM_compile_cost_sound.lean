-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_compile_cost_sound
-- name    : PandoraKnapsack.Skipping.ArrayRAM.compile_cost_sound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:48:53.297494+00:00
-- url     : https://prove2.me/theorems/8978e153-987a-46e9-b9ff-5302464150a6
-- title:
--   Soundness of counted real-RAM compilation
-- statement:
--   For any typed-array command $c$ executing in $k$ charged steps from the initial store, compilation produces a single program which, for every budget $B\ge7+k$, is halted and has the same decoded policy as the source output store. The seven steps are the input prologue. This statement holds on each draw stream.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and Theorem 5.1, Appendix B.1; original machine-implementation lemma for the stated Prove2Me exact coefficient-access model.

import Definitions.Def_PandoraKnapsack_Skipping_ArrayCompiler

namespace PandoraKnapsack.Skipping.ArrayRAM

theorem compile_cost_sound {n m T : ℕ} (I : Instance n m T) (ω : ℕ → ℝ)
    (c : C) (a : Store) (k B : ℕ) (e : Exec I ω c (initial n m T) a k) (hB : 7+k ≤ B) :
    Halted (compile c) (run I ω (compile c) B) ∧
      decodeOutput n m (run I ω (compile c) B).core.mem =
        decodeOutput n m (fun z => a.out z.toNat) := by sorry

end PandoraKnapsack.Skipping.ArrayRAM
