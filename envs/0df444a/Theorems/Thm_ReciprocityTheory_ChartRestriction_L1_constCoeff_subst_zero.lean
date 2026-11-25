-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_constCoeff_subst_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.constCoeff_subst_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:27:04.35599+00:00
-- url     : https://prove2.me/theorems/87712888-5d47-496b-9790-4810151d3bfe
-- title:
--   L1: const Coeff subst zero
-- statement:
--   The L1 construction uses the const Coeff subst zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L14-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
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

theorem ReciprocityTheory.ChartRestriction.L1.constCoeff_subst_zero {g s : PowerSeries R} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by sorry
