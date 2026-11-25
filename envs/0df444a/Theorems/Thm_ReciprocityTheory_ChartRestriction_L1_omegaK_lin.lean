-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_omegaK_lin
-- name    : ReciprocityTheory.ChartRestriction.L1.omegaK_lin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:48.348843+00:00
-- url     : https://prove2.me/theorems/6dbdf17c-4534-43aa-b6de-a8f02fc61b6f
-- title:
--   L1: omega K lin
-- statement:
--   The L1 construction uses the omega K lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModCMPoint.lean#L18-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModCMPoint.lean#L18-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
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

theorem ReciprocityTheory.ChartRestriction.L1.omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by sorry
