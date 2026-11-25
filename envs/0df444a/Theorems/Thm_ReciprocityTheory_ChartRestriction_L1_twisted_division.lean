-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_twisted_division
-- name    : ReciprocityTheory.ChartRestriction.L1.twisted_division
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:24.516692+00:00
-- url     : https://prove2.me/theorems/6011556a-582e-4ea9-9cf2-b0875c131baf
-- title:
--   L1: twisted division
-- statement:
--   The L1 construction uses the twisted division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L63-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L63-L109

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

theorem ReciprocityTheory.ChartRestriction.L1.twisted_division (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by sorry
