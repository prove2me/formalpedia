-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sub_pow_congr
-- name    : ReciprocityTheory.ChartRestriction.L1.sub_pow_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:52.583012+00:00
-- url     : https://prove2.me/theorems/cedb4949-53b5-4fdb-bab9-ecc5daec9cc3
-- title:
--   L1: sub pow congr
-- statement:
--   The L1 construction uses the sub pow congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobSer.lean#L46-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
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

theorem ReciprocityTheory.ChartRestriction.L1.sub_pow_congr {p : ℕ} (hp : p.Prime) (f g : PowerSeries ℤ) :
    ∃ w : PowerSeries ℤ, (f - g) ^ p = f ^ p - g ^ p + PowerSeries.C (p : ℤ) * w := by sorry
