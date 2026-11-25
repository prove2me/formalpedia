-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_odd
-- name    : ReciprocityTheory.ChartRestriction.L1.an_two_odd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:22.709903+00:00
-- url     : https://prove2.me/theorems/16554cbe-4eaf-4f42-8822-2d723cb5f06e
-- title:
--   L1: an two odd
-- statement:
--   The L1 construction uses the an two odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L76-L91

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

theorem ReciprocityTheory.ChartRestriction.L1.an_two_odd (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by sorry
