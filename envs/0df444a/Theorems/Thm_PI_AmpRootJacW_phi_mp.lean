-- Prove2me | Theorems.Thm_PI_AmpRootJacW_phi_mp
-- name    : PI.AmpRootJacW.phi_mp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:40.760255+00:00
-- url     : https://prove2.me/theorems/52dbf2ba-c0b9-55ed-8a0d-eea90c905222
-- title:
--   Amp Root Jac W: phi mp
-- statement:
--   The Amp Root Jac W construction uses the phi mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L165-L173

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

theorem PI.AmpRootJacW.phi_mp (S : Finset (Fin n × Fin n)) (hS : ∀ q ∈ S, q.1 < q.2) (τ : S ≃ S) (c : S → ℂ)
    (hc : ∀ q, ‖c q‖ = 1) :
    MeasurePreserving (fun (v : S → ℂ) q => c q * star (invC S v (τ q))) volume volume := by sorry
