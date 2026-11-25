-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_gs_other
-- name    : ReciprocityTheory.ReducedBases.T2.swap_gs_other
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:45.389632+00:00
-- url     : https://prove2.me/theorems/d82e4d95-b412-577c-a302-b0676f1ea98e
-- title:
--   T2: swap gs other
-- statement:
--   The T2 construction uses the swap gs other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L42-L52

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

theorem ReciprocityTheory.ReducedBases.T2.swap_gs_other (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j) (hk1 : k ≠ j1) : gs (b ∘ Equiv.swap j j1) k = gs b k := by sorry
