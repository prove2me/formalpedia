-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_triIter_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.triIter_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:47:24.539045+00:00
-- url     : https://prove2.me/theorems/77773378-6e88-46c4-8d73-3a00c7ce420a
-- title:
--   L1: tri Iter norm
-- statement:
--   The L1 construction uses the tri Iter norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L46-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
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
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem ReciprocityTheory.ChartRestriction.L1.triIter_norm (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by sorry
