-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pderiv_ts
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_ts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:57.057009+00:00
-- url     : https://prove2.me/theorems/2ffe0fa8-d0b5-4fb6-9599-bda65ddc9671
-- title:
--   Simeq Pd Int: pderiv ts
-- statement:
--   The Simeq Pd Int construction uses the pderiv ts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L35-L49

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

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_ts (k : σ) (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    pderiv ℂ_[p] k (ts f (N + 1)) = ts f N * pderiv ℂ_[p] k f := by sorry
