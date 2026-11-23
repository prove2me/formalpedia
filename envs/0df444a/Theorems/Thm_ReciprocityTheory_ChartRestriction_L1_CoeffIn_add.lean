-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
-- name    : ReciprocityTheory.ChartRestriction.L1.CoeffIn.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:57.962802+00:00
-- url     : https://prove2.me/theorems/3c85dc42-d7c9-4b47-b85b-9091b7ea19a7
-- title:
--   Coeff In: add
-- statement:
--   The Coeff In construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L55-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add

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

theorem ReciprocityTheory.ChartRestriction.L1.CoeffIn.add {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f + g) := by sorry
