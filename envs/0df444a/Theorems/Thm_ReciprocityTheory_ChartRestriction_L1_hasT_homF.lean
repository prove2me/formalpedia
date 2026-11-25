-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hasT_homF
-- name    : ReciprocityTheory.ChartRestriction.L1.hasT_homF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:47:42.618997+00:00
-- url     : https://prove2.me/theorems/915cde9e-0f45-47c7-9052-d5940d5c5d0d
-- title:
--   L1: has T hom F
-- statement:
--   The L1 construction uses the has T hom F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L70-L72

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

theorem ReciprocityTheory.ChartRestriction.L1.hasT_homF {u : ℂ → ℂ} {U : PowerSeries ℂ} (hu : HasT u U) (m : ℕ) (Q : ℂ[X]) :
    HasT (homF u m Q) (homS U m Q) := by sorry
