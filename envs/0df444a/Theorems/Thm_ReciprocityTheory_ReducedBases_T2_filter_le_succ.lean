-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_filter_le_succ
-- name    : ReciprocityTheory.ReducedBases.T2.filter_le_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:29.104889+00:00
-- url     : https://prove2.me/theorems/d3bf620a-4769-4e73-aa3e-daa6c3b2b8ec
-- title:
--   T2: filter le succ
-- statement:
--   The T2 construction uses the filter le succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L123-L128

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
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
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.filter_le_succ (n : ℕ) (h : n + 1 < d) :
    univ.filter (fun j : Fin d => j.val ≤ n + 1) =
      insert ⟨n + 1, h⟩ (univ.filter (fun j : Fin d => j.val ≤ n)) := by sorry
