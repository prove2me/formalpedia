-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.simeq_ren
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:52.918451+00:00
-- url     : https://prove2.me/theorems/6b95498e-aabe-4b01-80e4-b71331bd4a23
-- title:
--   Ph Dual Gram: simeq ren
-- statement:
--   The Ph Dual Gram construction uses the simeq ren property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L55-L68

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.simeq_ren {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq (ren r f) (ren r g) := by sorry
