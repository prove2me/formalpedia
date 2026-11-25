-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_unit_prod
-- name    : ReciprocityTheory.ChartRestriction.L1.unit_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:42.673102+00:00
-- url     : https://prove2.me/theorems/96ae4b1d-dcab-54b2-9426-fd77d0efd0bf
-- title:
--   L1: unit prod
-- statement:
--   The L1 construction uses the unit prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValB.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedValB.lean#L40-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledTorsionPointNonsingular
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.unit_prod (L : PeriodPair) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (h5 : 5 ≤ l) (μ : ℂ_[l])
    (hμ : μ ^ 12 * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1) (hg2 : ‖μ ^ 4 * ι L.g₂‖ ≤ 1)
    (hg3 : ‖μ ^ 6 * ι L.g₃‖ ≤ 1) (e N : ℕ)
    (he : e = 3 ∧ ‖μ ^ 4 * ι L.g₂‖ < 1 ∨ e = 2 ∧ ‖μ ^ 6 * ι L.g₃‖ < 1) (hlN : ¬ l ∣ N) (heN : ¬ e ∣ N)
    (T : Finset ℂ) (hT : ∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) :
    ‖μ‖ ^ (2 * T.card) * ‖ι (∏ z ∈ T, L.weierstrassP z)‖ = 1 := by sorry
