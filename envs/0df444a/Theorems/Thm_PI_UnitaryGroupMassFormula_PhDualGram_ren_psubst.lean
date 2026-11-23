-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.ren_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:00.300901+00:00
-- url     : https://prove2.me/theorems/aaeb899f-2d1d-4175-a362-1cd140175264
-- title:
--   Ph Dual Gram: ren psubst
-- statement:
--   The Ph Dual Gram construction uses the ren psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L43-L47

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.ren_psubst (P : PowerSeries ℂ_[p]) {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    ren r (PowerSeries.subst y P) = PowerSeries.subst (ren r y) P := by sorry
