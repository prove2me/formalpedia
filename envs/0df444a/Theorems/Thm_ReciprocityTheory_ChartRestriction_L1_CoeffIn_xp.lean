-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
-- name    : ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:12.619536+00:00
-- url     : https://prove2.me/theorems/34dd9c1b-d0cd-4cad-8750-1f33a9e0a24d
-- title:
--   Coeff In: xp
-- statement:
--   The Coeff In construction uses the xp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L93-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
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

theorem ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by sorry
