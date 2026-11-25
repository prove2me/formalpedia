-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hasT_sum
-- name    : ReciprocityTheory.ChartRestriction.L1.hasT_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:56.860971+00:00
-- url     : https://prove2.me/theorems/79d3282f-ff55-4fee-9e8a-a2070c0befe2
-- title:
--   L1: has T sum
-- statement:
--   The L1 construction uses the has T sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L34-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.hasT_sum {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ι → PowerSeries ℂ)
    (h : ∀ i ∈ S, HasT (f i) (s i)) : HasT (fun z => ∑ i ∈ S, f i z) (∑ i ∈ S, s i) := by sorry
