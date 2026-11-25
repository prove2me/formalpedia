-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_term
-- name    : ReciprocityTheory.ChartRestriction.L1.xp_term
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:33.555829+00:00
-- url     : https://prove2.me/theorems/d6df047d-549b-4233-b090-36d591412246
-- title:
--   L1: xp term
-- statement:
--   The L1 construction uses the xp term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L106-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp

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

theorem ReciprocityTheory.ChartRestriction.L1.xp_term (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) (m : ℕ) :
    PowerSeries.coeff (k * m) (xp k f) * x ^ (k * m) = PowerSeries.coeff m f * (x ^ k) ^ m := by sorry
