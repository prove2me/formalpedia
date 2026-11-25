-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hasUnitLeadingCoeff_rescaleExpand_discriminantSeries
-- name    : ReciprocityTheory.ChartRestriction.L1.hasUnitLeadingCoeff_rescaleExpand_discriminantSeries
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:56.971817+00:00
-- url     : https://prove2.me/theorems/202087f0-e84f-49a3-b38f-deb3d7d66a6c
-- title:
--   L1: has Unit Leading Coeff rescale Expand discriminant Series
-- statement:
--   The L1 construction uses the has Unit Leading Coeff rescale Expand discriminant Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSer.lean#L150-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSer.lean#L150-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1

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

theorem ReciprocityTheory.ChartRestriction.L1.hasUnitLeadingCoeff_rescaleExpand_discriminantSeries {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by sorry
