-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_one_desc
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_one_desc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:57.081964+00:00
-- url     : https://prove2.me/theorems/48b5eaa9-83cc-57c0-b0f9-06f192ab5e00
-- title:
--   L1: coeff one desc
-- statement:
--   The L1 construction uses the coeff one desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonC.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonC.lean#L23-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem ReciprocityTheory.ChartRestriction.L1.coeff_one_desc (D : PowerSeries K) : coeff 1 (desc l D) = coeff l D := by sorry
