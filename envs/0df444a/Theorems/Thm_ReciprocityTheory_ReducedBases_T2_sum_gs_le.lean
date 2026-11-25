-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_sum_gs_le
-- name    : ReciprocityTheory.ReducedBases.T2.sum_gs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:37.670479+00:00
-- url     : https://prove2.me/theorems/4440799e-53ec-4191-9ccd-c4fa811c7acd
-- title:
--   T2: sum gs le
-- statement:
--   The T2 construction uses the sum gs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L137-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L137-L162

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

theorem ReciprocityTheory.ReducedBases.T2.sum_gs_le (b : Fin d → E)
    (hl : ∀ i j : Fin d, i.val = j.val + 1 → ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2) :
    ∀ (n : ℕ) (h : n < d), ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ n), ‖gs b j‖ ^ 2 ≤
      (2 ^ (n + 1) - 1) * ‖gs b ⟨n, h⟩‖ ^ 2 := by sorry
