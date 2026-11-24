-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.evalYZero_subst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:52.786736+00:00
-- url     : https://prove2.me/theorems/4028817f-778e-4966-a956-6db16f6291c4
-- title:
--   L1: eval YZero subst
-- statement:
--   The L1 construction uses the eval YZero subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L53-L62

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

theorem ReciprocityTheory.ChartRestriction.L1.evalYZero_subst (φ : PowerSeries R) {P : MvPowerSeries (Fin 2) R}
    (hP : MvPowerSeries.constantCoeff P = 0) : ev0 (φ.subst P) = φ.subst (ev0 P) := by sorry
