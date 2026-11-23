-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_swap_j
-- name    : ReciprocityTheory.ReducedBases.T2.norm_swap_j
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:01.470466+00:00
-- url     : https://prove2.me/theorems/afbd5649-cb6d-402f-a949-5d9e2e7d2ee4
-- title:
--   T2: norm swap j
-- statement:
--   The T2 construction uses the norm swap j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L92-L97

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

theorem ReciprocityTheory.ReducedBases.T2.norm_swap_j (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) :
    ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by sorry
