-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.LowUnit.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:33.253876+00:00
-- url     : https://prove2.me/theorems/0f9ebcb4-d230-4141-8176-fd0645fe7db4
-- title:
--   Low Unit: mul
-- statement:
--   The Low Unit construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L107-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L107-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul

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

theorem ReciprocityTheory.ChartRestriction.L1.LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') (u * u') := by sorry
