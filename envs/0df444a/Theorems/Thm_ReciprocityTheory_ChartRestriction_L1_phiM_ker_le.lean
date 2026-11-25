-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_phiM_ker_le
-- name    : ReciprocityTheory.ChartRestriction.L1.phiM_ker_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:10.171242+00:00
-- url     : https://prove2.me/theorems/c9d63f98-de9f-49bd-aa11-7ccd4eca2431
-- title:
--   L1: phi M ker le
-- statement:
--   The L1 construction uses the phi M ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L71-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by sorry
