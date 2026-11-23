-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.IsMF.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:38.608119+00:00
-- url     : https://prove2.me/theorems/65520e8c-2b86-45a0-8f58-7ec8df1022dd
-- title:
--   Is MF: mul
-- statement:
--   The Is MF construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModBasic.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModBasic.lean#L98-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by sorry
