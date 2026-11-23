-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_PhOn
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.ren_PhOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:11.073164+00:00
-- url     : https://prove2.me/theorems/eb5d374c-759c-4f3a-b531-f77ef33a25ec
-- title:
--   Ph Dual Gram: ren Ph On
-- statement:
--   The Ph Dual Gram construction uses the ren Ph On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L94-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L94-L111

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
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
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)
omit [Finite σ]
include hex0 hl0

theorem PI.UnitaryGroupMassFormula.PhDualGram.ren_PhOn {κ T : Type} [Fintype κ] [Fintype T] {n : ℕ} (E : T ≃ Fin n)
    (B : T → κ → ℂ_[p] × ℂ_[p]) :
    ren (p := p) E.symm (PhOn l ex ph (fun j => B (E.symm j))) = PhOn l ex ph B := by sorry
