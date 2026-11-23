-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_img
-- name    : ReciprocityTheory.ReducedBases.T2.swap_img
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:55.706798+00:00
-- url     : https://prove2.me/theorems/ae259d94-a48f-44dd-a63c-b9f176c68f18
-- title:
--   T2: swap img
-- statement:
--   The T2 construction uses the swap img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L30-L40

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

theorem ReciprocityTheory.ReducedBases.T2.swap_img (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j1) : (b ∘ Equiv.swap j j1) '' Set.Iio k = b '' Set.Iio k := by sorry
