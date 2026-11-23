-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_C
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.ren_C
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:52.683808+00:00
-- url     : https://prove2.me/theorems/f6b2231f-135b-46d5-8436-28a5bebe185a
-- title:
--   Ph Dual Gram: ren C
-- statement:
--   The Ph Dual Gram construction uses the ren C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L52-L53

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

theorem PI.UnitaryGroupMassFormula.PhDualGram.ren_C (c : ℂ_[p]) : ren r (C c : MvPowerSeries σ ℂ_[p]) = C c := by sorry
