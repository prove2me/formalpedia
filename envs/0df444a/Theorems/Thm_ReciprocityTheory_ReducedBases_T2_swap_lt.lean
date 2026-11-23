-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_lt
-- name    : ReciprocityTheory.ReducedBases.T2.swap_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:24.744187+00:00
-- url     : https://prove2.me/theorems/db13f5f3-88ca-4f03-a8e9-a554fd1c52d5
-- title:
--   T2: swap lt
-- statement:
--   The T2 construction uses the swap lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean#L14-L28

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

theorem ReciprocityTheory.ReducedBases.T2.swap_lt (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d) (hk : k ≠ j1) (l : Fin d)
    (hl : l < k) : Equiv.swap j j1 l < k := by sorry
