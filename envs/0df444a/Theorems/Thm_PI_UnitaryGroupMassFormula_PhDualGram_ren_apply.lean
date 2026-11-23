-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.ren_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:20.814569+00:00
-- url     : https://prove2.me/theorems/55771caf-e8f1-4dd8-9a89-090ecaf20385
-- title:
--   Ph Dual Gram: ren apply
-- statement:
--   The Ph Dual Gram construction uses the ren apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L39-L41

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.ren_apply (F : MvPowerSeries σ ℂ_[p]) :
    ren r F = MvPowerSeries.subst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) F := by sorry
