-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_gramRhs_dual
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.gramRhs_dual
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:34.598143+00:00
-- url     : https://prove2.me/theorems/9e4d6416-e2fb-481b-8a3d-6d4f854293b4
-- title:
--   Ph Dual Gram: gram Rhs dual
-- statement:
--   The Ph Dual Gram construction uses the gram Rhs dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L45-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L45-L76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem PI.UnitaryGroupMassFormula.PhDualGram.gramRhs_dual (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {κ ι : Type} [Fintype κ] [Fintype ι]
    (b b' : ι → κ → ℂ_[p] × ℂ_[p]) (hI : DualIso b b') {n : ℕ} (E : ι ⊕ ι ≃ Fin n)
    (hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e')) :
    GramRhs l ex ph (fun j => Sum.elim b b' (E.symm j)) =
      ∑ e, be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e))) := by sorry
