-- Prove2me | Theorems.Thm_P2M_PI_FglShared_expMv_add__f0eb8b5a05d0
-- name    : P2M_PI_FglShared_expMv_add__f0eb8b5a05d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:36.454818+00:00
-- url     : https://prove2.me/theorems/eeb36355-10b1-4d04-9d52-c53f770c2e07
-- title:
--   P2 M PI Fgl Shared exp Mv add  f0eb8b5a05d0: P2 M PI Fgl Shared exp Mv add  f0eb8b5a05d0
-- statement:
--   The P2 M PI Fgl Shared exp Mv add  f0eb8b5a05d0 construction uses the P2 M PI Fgl Shared exp Mv add  f0eb8b5a05d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L78-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_FglShared_expMv_add__f0eb8b5a05d0 {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : PI.FglPhSplit.expMv (f + g) = PI.FglPhSplit.expMv f * PI.FglPhSplit.expMv g := by sorry

alias «PI».«FglShared».«expMv_add'» := P2M_PI_FglShared_expMv_add__f0eb8b5a05d0
