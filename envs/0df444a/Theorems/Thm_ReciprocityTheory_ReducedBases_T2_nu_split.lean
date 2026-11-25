-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_split
-- name    : ReciprocityTheory.ReducedBases.T2.nu_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:58.912372+00:00
-- url     : https://prove2.me/theorems/79a5f3d6-c084-4355-b71f-b2db4293b89f
-- title:
--   T2: nu split
-- statement:
--   The T2 construction uses the nu split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L75-L77

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

theorem ReciprocityTheory.ReducedBases.T2.nu_split (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    nu b c j = c j + ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j := by sorry
