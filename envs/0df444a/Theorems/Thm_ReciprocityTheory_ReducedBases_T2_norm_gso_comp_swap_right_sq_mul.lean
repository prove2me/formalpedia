-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_gso_comp_swap_right_sq_mul
-- name    : ReciprocityTheory.ReducedBases.T2.norm_gso_comp_swap_right_sq_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:51.080806+00:00
-- url     : https://prove2.me/theorems/de08ca54-f00a-599f-b105-c7961b63c506
-- title:
--   T2: norm gso comp swap right sq mul
-- statement:
--   The T2 construction uses the norm gso comp swap right sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L99-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L99-L159

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.norm_gso_comp_swap_right_sq_mul (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    ‖gs (b ∘ Equiv.swap j j1) j1‖ ^ 2 * ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 =
      ‖gs b j‖ ^ 2 * ‖gs b j1‖ ^ 2 := by sorry
