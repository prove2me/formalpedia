-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_triSol_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.triSol_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:30.015674+00:00
-- url     : https://prove2.me/theorems/452d7932-f311-5215-ba7f-6b212d400856
-- title:
--   L1: tri Sol norm
-- statement:
--   The L1 construction uses the tri Sol norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean#L22-L34

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

theorem ReciprocityTheory.ChartRestriction.L1.triSol_norm (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by sorry
