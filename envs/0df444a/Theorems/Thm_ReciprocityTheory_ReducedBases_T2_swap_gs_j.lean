-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_gs_j
-- name    : ReciprocityTheory.ReducedBases.T2.swap_gs_j
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:08.242211+00:00
-- url     : https://prove2.me/theorems/c491a017-589f-47fd-a7a2-03b4597462e6
-- title:
--   T2: swap gs j
-- statement:
--   The T2 construction uses the swap gs j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L54-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L54-L90

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

theorem ReciprocityTheory.ReducedBases.T2.swap_gs_j (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    gs (b ∘ Equiv.swap j j1) j = gs b j1 + mu b j1 j • gs b j := by sorry
