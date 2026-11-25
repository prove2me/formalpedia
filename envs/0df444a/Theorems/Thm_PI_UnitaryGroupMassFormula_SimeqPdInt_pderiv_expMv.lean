-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pderiv_expMv
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_expMv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:28.502251+00:00
-- url     : https://prove2.me/theorems/d73c8d58-166b-4303-9beb-fab05efc5e53
-- title:
--   Simeq Pd Int: pderiv exp Mv
-- statement:
--   The Simeq Pd Int construction uses the pderiv exp Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L51-L64

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

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_expMv (k : σ) {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) :
    pderiv ℂ_[p] k (PI.FglGram.expMv f) = PI.FglGram.expMv f * pderiv ℂ_[p] k f := by sorry
