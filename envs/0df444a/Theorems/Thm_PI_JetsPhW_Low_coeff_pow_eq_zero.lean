-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_pow_eq_zero
-- name    : PI.JetsPhW.Low.coeff_pow_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:34.586653+00:00
-- url     : https://prove2.me/theorems/caf28682-e1c6-4e70-adf0-52e458a82d3d
-- title:
--   Low: coeff pow eq zero
-- statement:
--   The Low construction uses the coeff pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L9-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]

theorem PI.JetsPhW.Low.coeff_pow_eq_zero {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    ∀ (d : ℕ) (e : σ →₀ ℕ), Finsupp.degree e < d → MvPowerSeries.coeff e (A ^ d) = 0
  := by sorry
