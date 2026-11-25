-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_block_simeq
-- name    : PI.UnitaryGroupMassFormula.SDiffGram.block_simeq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:33.533508+00:00
-- url     : https://prove2.me/theorems/ff02d602-7a7f-4693-ab49-f1bdd288a340
-- title:
--   SDiff Gram: block simeq
-- statement:
--   The SDiff Gram construction uses the block simeq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L16-L28

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

theorem PI.UnitaryGroupMassFormula.SDiffGram.block_simeq (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])}
    (hG : ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A))
    {κ T τ : Type} [Fintype κ] [Fintype T] {n : ℕ} (e : T ≃ Fin n) (r : T → τ)
    (a : T → κ → ℂ_[p] × ℂ_[p]) (ha : ∀ x k, a x k ∈ S) :
    Simeq (PhVF l ex ph a (fun x => X (r x))) (GR l ex ph e a (fun x => X (r x))) := by sorry
