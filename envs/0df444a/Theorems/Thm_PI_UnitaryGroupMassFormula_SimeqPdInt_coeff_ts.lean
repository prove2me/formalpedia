-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_coeff_ts
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_ts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:21.544301+00:00
-- url     : https://prove2.me/theorems/11a3efe7-2eb6-4a1d-95b5-e5b30f0708f2
-- title:
--   Simeq Pd Int: coeff ts
-- statement:
--   The Simeq Pd Int construction uses the coeff ts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L23-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (a : σ →₀ ℕ) :
    coeff a (ts f N) = ∑ n ∈ Finset.range N, coeff a (f ^ n) / (n.factorial : ℂ_[p]) := by sorry
