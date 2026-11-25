-- Prove2me | Theorems.Thm_PI_AmpRootJacW_shear_mp
-- name    : PI.AmpRootJacW.shear_mp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:39.384157+00:00
-- url     : https://prove2.me/theorems/a7bf451b-e07d-4d26-8616-ffac954c450b
-- title:
--   Amp Root Jac W: shear mp
-- statement:
--   The Amp Root Jac W construction uses the shear mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L136-L139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))

theorem PI.AmpRootJacW.shear_mp (hS : ∀ q ∈ S, q.1 < q.2) :
    MeasurePreserving (fun v : S → ℂ => fun q => v q + hSh S q v) volume volume := by sorry
