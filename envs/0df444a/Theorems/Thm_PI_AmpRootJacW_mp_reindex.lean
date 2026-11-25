-- Prove2me | Theorems.Thm_PI_AmpRootJacW_mp_reindex
-- name    : PI.AmpRootJacW.mp_reindex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:23.115204+00:00
-- url     : https://prove2.me/theorems/78f742b6-993c-549b-b404-5b5cdcc6abfb
-- title:
--   Amp Root Jac W: mp reindex
-- statement:
--   The Amp Root Jac W construction uses the mp reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L143-L149

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

theorem PI.AmpRootJacW.mp_reindex {ι : Type} [Fintype ι] (τ : ι ≃ ι) :
    MeasurePreserving (fun (w : ι → ℂ) i => w (τ i)) volume volume := by sorry
