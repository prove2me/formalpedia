-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_xp
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_xp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:48.778077+00:00
-- url     : https://prove2.me/theorems/f4aecc34-f696-430a-8274-b23b75833353
-- title:
--   L1: coeff xp
-- statement:
--   The L1 construction uses the coeff xp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L11-L13

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

theorem ReciprocityTheory.ChartRestriction.L1.coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by sorry
