-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_coeff_expMv_eq_ts
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_expMv_eq_ts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:49.27741+00:00
-- url     : https://prove2.me/theorems/05d68c4f-3299-46b8-939e-20aab8f63a47
-- title:
--   Simeq Pd Int: coeff exp Mv eq ts
-- statement:
--   The Simeq Pd Int construction uses the coeff exp Mv eq ts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L29-L33

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

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_expMv_eq_ts {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    {a : σ →₀ ℕ} {N : ℕ} (h : a.degree ≤ N) :
    coeff a (PI.FglGram.expMv f) = coeff a (ts f (N + 1)) := by sorry
