-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_coeff_subst_of_degree_eq_one
-- name    : PI.JetsPhW.Low.coeff_subst_of_degree_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:35.319351+00:00
-- url     : https://prove2.me/theorems/69d0fe7e-ce95-4244-a38a-432b8181b432
-- title:
--   Low: coeff subst of degree eq one
-- statement:
--   The Low construction uses the coeff subst of degree eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L60-L67

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

theorem PI.JetsPhW.Low.coeff_subst_of_degree_eq_one {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A := by sorry
