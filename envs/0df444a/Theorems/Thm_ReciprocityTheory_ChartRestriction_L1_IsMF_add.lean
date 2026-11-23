-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add
-- name    : ReciprocityTheory.ChartRestriction.L1.IsMF.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:54.255232+00:00
-- url     : https://prove2.me/theorems/d7fc9aa3-3205-4855-830d-83d089fd58f0
-- title:
--   Is MF: add
-- statement:
--   The Is MF construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModBasic.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModBasic.lean#L84-L87

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

theorem ReciprocityTheory.ChartRestriction.L1.IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by sorry
