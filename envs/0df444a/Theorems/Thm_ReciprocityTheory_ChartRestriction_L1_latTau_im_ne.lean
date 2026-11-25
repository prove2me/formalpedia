-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_latTau_im_ne
-- name    : ReciprocityTheory.ChartRestriction.L1.latTau_im_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:59.039789+00:00
-- url     : https://prove2.me/theorems/c40e40a1-cd2b-50f1-acb6-7222f3f3d045
-- title:
--   L1: lat Tau im ne
-- statement:
--   The L1 construction uses the lat Tau im ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLatTau.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLatTau.lean#L13-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
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

theorem ReciprocityTheory.ChartRestriction.L1.latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by sorry
