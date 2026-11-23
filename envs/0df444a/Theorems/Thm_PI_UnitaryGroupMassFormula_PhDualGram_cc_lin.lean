-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.cc_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:10.836805+00:00
-- url     : https://prove2.me/theorems/9c67fe16-60c9-4448-90f4-34bc186d60cc
-- title:
--   Ph Dual Gram: cc lin
-- statement:
--   The Ph Dual Gram construction uses the cc lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean#L75-L80

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
include hl0

theorem PI.UnitaryGroupMassFormula.PhDualGram.cc_lin {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    constantCoeff (∑ j, C (c j) * lg l (w j)) = 0 := by sorry
