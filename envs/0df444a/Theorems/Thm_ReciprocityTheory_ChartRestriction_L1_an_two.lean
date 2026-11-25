-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two
-- name    : ReciprocityTheory.ChartRestriction.L1.an_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:04.782601+00:00
-- url     : https://prove2.me/theorems/58c378d5-ff68-5dbc-914c-849b2a61e041
-- title:
--   L1: an two
-- statement:
--   The L1 construction uses the an two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L104-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgAnTwo.lean#L104-L138

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

theorem ReciprocityTheory.ChartRestriction.L1.an_two (L : PeriodPair) (n : ℕ) (hn : Odd n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    ((n : ℂ) ^ 2 * ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P)) ^ 2
      = (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) ^ (n ^ 2 - 1) := by sorry
