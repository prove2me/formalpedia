-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.ren_be
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:57.555336+00:00
-- url     : https://prove2.me/theorems/f6deb9f2-26c0-49e4-a9fa-4df376c16374
-- title:
--   Ph Dual Gram: ren be
-- statement:
--   The Ph Dual Gram construction uses the ren be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/BeMulByZero.lean#L20-L29

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.ren_be (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ τ : Type} [Finite σ] (r : σ → τ) {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    ren r (be l ex ph x y) = be l ex ph (ren r x) (ren r y) := by sorry
