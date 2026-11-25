-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_pot_swap
-- name    : ReciprocityTheory.ReducedBases.T2.pot_swap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:10.756676+00:00
-- url     : https://prove2.me/theorems/4b600645-d7d1-471a-8ec1-746430880bfd
-- title:
--   T2: pot swap
-- statement:
--   The T2 construction uses the pot swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L179-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L179-L214

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

theorem ReciprocityTheory.ReducedBases.T2.pot_swap (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    pot (b ∘ Equiv.swap j j1) =
      pot b * (‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2) := by sorry
