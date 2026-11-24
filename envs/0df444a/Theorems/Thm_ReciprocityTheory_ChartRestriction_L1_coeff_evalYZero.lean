-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_evalYZero
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_evalYZero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:23.795328+00:00
-- url     : https://prove2.me/theorems/f674df5a-ff4f-4413-bd2a-22bec0ce1846
-- title:
--   L1: coeff eval YZero
-- statement:
--   The L1 construction uses the coeff eval YZero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L17-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L17-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
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
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.L1.coeff_evalYZero (F : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff n (ev0 F) = MvPowerSeries.coeff (Finsupp.single 0 n) F := by sorry
