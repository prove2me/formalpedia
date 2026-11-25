-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eventually_notMem
-- name    : ReciprocityTheory.ChartRestriction.L1.eventually_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:25.694358+00:00
-- url     : https://prove2.me/theorems/b8343731-bc0d-52a8-a13f-b74473573f0c
-- title:
--   L1: eventually not Mem
-- statement:
--   The L1 construction uses the eventually not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L82-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eventually_notMem

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

theorem ReciprocityTheory.ChartRestriction.L1.eventually_notMem (L : PeriodPair) {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 ∧ α * z ∉ L.lattice := by sorry
