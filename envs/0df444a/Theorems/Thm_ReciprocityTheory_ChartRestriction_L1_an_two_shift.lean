-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_shift
-- name    : ReciprocityTheory.ChartRestriction.L1.an_two_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:18:48.945116+00:00
-- url     : https://prove2.me/theorems/ba4b7866-ea80-4c87-8b08-d897e3bcbdfb
-- title:
--   L1: an two shift
-- statement:
--   The L1 construction uses the an two shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L11-L22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgAnTwo
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
open Formalism.L2.Th1
open scoped ComplexConjugate

theorem ReciprocityTheory.ChartRestriction.L1.an_two_shift (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by sorry
