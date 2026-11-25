-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_ccX
-- name    : PI.BiaddZpLinW.ccX
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:49.19538+00:00
-- url     : https://prove2.me/theorems/339d5d66-e6c4-4ed9-9324-dffce3deb451
-- title:
--   Biadd Zp Lin W: cc X
-- statement:
--   The Biadd Zp Lin W construction uses the cc X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L81-L82

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiaddZpLinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BiaddZpLinW
open PI.BiaddZpLin
variable {p : ℕ} [Fact p.Prime]

theorem PI.BiaddZpLinW.ccX {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by sorry
