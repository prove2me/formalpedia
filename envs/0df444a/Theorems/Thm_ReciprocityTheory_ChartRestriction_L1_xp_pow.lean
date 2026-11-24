-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_pow
-- name    : ReciprocityTheory.ChartRestriction.L1.xp_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:31:17.188899+00:00
-- url     : https://prove2.me/theorems/72a1ce8c-e527-4b87-9a0f-7ae103982c4c
-- title:
--   L1: xp pow
-- statement:
--   The L1 construction uses the xp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffRescaleExpandOfNotDvd.lean#L34-L36

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

theorem ReciprocityTheory.ChartRestriction.L1.xp_pow {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    xp k (f ^ n) = xp k f ^ n := by sorry
