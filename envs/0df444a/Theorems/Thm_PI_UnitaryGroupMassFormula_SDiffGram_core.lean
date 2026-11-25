-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_core
-- name    : PI.UnitaryGroupMassFormula.SDiffGram.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:46.436871+00:00
-- url     : https://prove2.me/theorems/db55a4b2-3af8-4850-a725-acb7f3c8061d
-- title:
--   SDiff Gram: core
-- statement:
--   The SDiff Gram construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L79-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/SDiffGramMain.lean#L79-L112

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

theorem PI.UnitaryGroupMassFormula.SDiffGram.core (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])} (h0 : (0 : ℂ_[p] × ℂ_[p]) ∈ S) (hsw : ∀ α ∈ S, α.swap ∈ S)
    (hadd : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    (hG : ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A))
    (hconj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1))))
    {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p])
    (ha : ∀ e k, a e k ∈ S) (ha' : ∀ e k, a' e k ∈ S) :
    Simeq (PhOn l ex ph (Sum.elim a a') - PhVF l ex ph a (fun e => X (Sum.inl e)) -
        PhVF l ex ph a' (fun e => X (Sum.inr e))) (sdRF l ex ph a a') ∧
    Simeq (PhOn l ex ph (Sum.elim a a') - PhVF l ex ph a (fun e => X (Sum.inl e)) -
        PhVF l ex ph a' (fun e => X (Sum.inr e))) (sdRF' l ex ph a a') := by sorry
