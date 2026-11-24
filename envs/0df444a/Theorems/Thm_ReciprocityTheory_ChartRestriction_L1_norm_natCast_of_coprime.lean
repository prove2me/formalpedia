-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_of_coprime
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_natCast_of_coprime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:31.130361+00:00
-- url     : https://prove2.me/theorems/dac1c880-b04b-441a-a729-6002de3e3cb0
-- title:
--   L1: norm nat Cast of coprime
-- statement:
--   The L1 construction uses the norm nat Cast of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L417-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L417-L450

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {l : ℕ} {σ : K →+* K} {ι : Type}

theorem ReciprocityTheory.ChartRestriction.L1.norm_natCast_of_coprime (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (m : ℕ) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by sorry
