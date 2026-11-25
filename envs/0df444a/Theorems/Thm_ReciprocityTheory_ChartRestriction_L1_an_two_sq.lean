-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_sq
-- name    : ReciprocityTheory.ChartRestriction.L1.an_two_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:15.612567+00:00
-- url     : https://prove2.me/theorems/1eef5192-d42c-5523-8771-4e6597625f61
-- title:
--   L1: an two sq
-- statement:
--   The L1 construction uses the an two sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L24-L31

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

theorem ReciprocityTheory.ChartRestriction.L1.an_two_sq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by sorry
