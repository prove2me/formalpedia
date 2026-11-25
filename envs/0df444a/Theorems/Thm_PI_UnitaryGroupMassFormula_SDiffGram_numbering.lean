-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_numbering
-- name    : PI.UnitaryGroupMassFormula.SDiffGram.numbering
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:00.094186+00:00
-- url     : https://prove2.me/theorems/fa50589c-a79b-4c25-86ed-0af4288360b0
-- title:
--   SDiff Gram: numbering
-- statement:
--   The SDiff Gram construction uses the numbering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L30-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L30-L54

import Definitions.Def_Formalism_PeriodIntegrals_SDiffGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_SDiffGramMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_X simeq_ren ren_be)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem PI.UnitaryGroupMassFormula.SDiffGram.numbering (ι ι' : Type) [Fintype ι] [Fintype ι'] :
    ∃ (E : ι ⊕ ι' ≃ Fin (Fintype.card ι + Fintype.card ι')) (eι : ι ≃ Fin (Fintype.card ι))
      (eι' : ι' ≃ Fin (Fintype.card ι')),
      (∀ i i', E (Sum.inl i) < E (Sum.inl i') ↔ eι i < eι i') ∧
      (∀ g g', E (Sum.inr g) < E (Sum.inr g') ↔ eι' g < eι' g') ∧
      (∀ i g, E (Sum.inl i) < E (Sum.inr g)) ∧ (∀ g i, ¬ E (Sum.inr g) < E (Sum.inl i)) := by sorry
