-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_le
-- name    : ReciprocityTheory.ChartRestriction.L1.kur_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:29.317684+00:00
-- url     : https://prove2.me/theorems/11fb2dee-8191-58f4-852a-ceb601535eca
-- title:
--   L1: kur le
-- statement:
--   The L1 construction uses the kur le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocB.lean#L50-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocB.lean#L50-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.kur_le {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : PadicAlgCl l}
    (hs : s ^ 2 = -(d : PadicAlgCl l)) {y : PadicAlgCl l}
    (hy : y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s})) :
    algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by sorry
