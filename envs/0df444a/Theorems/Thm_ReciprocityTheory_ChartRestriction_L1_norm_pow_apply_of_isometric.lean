-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_pow_apply_of_isometric
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_pow_apply_of_isometric
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:37.811697+00:00
-- url     : https://prove2.me/theorems/a9b6d4dc-18d5-4140-a8bb-7411b219b976
-- title:
--   L1: norm pow apply of isometric
-- statement:
--   The L1 construction uses the norm pow apply of isometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L36-L40

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

theorem ReciprocityTheory.ChartRestriction.L1.norm_pow_apply_of_isometric (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by sorry
