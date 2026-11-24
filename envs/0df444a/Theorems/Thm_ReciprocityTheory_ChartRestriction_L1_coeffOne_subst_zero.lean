-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeffOne_subst_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.coeffOne_subst_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:33.566242+00:00
-- url     : https://prove2.me/theorems/c5196678-1965-40d4-88bf-d85fc8c3d63f
-- title:
--   L1: coeff One subst zero
-- statement:
--   The L1 construction uses the coeff One subst zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L22-L35

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

theorem ReciprocityTheory.ChartRestriction.L1.coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by sorry
