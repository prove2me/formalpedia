-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_kap
-- name    : ReciprocityTheory.ChartRestriction.L1.an_two_kap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:22.204311+00:00
-- url     : https://prove2.me/theorems/f200df1a-a919-4065-b8ae-34a855dcf81c
-- title:
--   L1: an two kap
-- statement:
--   The L1 construction uses the an two kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L33-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L33-L74

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

theorem ReciprocityTheory.ChartRestriction.L1.an_two_kap (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by sorry
