-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_natCase
-- name    : PI.BiaddZpLinW.natCase
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:33.187908+00:00
-- url     : https://prove2.me/theorems/24035e7b-08b3-4de1-a827-48b2b1eddd62
-- title:
--   Biadd Zp Lin W: nat Case
-- statement:
--   The Biadd Zp Lin W construction uses the nat Case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L84-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L84-L186

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

theorem PI.BiaddZpLinW.natCase (l ex ph : PowerSeries ℂ_[p]) (hex : PowerSeries.constantCoeff ex = 0)
    (hlex : PowerSeries.subst ex l = PowerSeries.X)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (n : ℕ) :
    IntegralMv (mulBy l ex (n : ℂ_[p]) (Xv 0) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    Simeq (be l ex ph (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1)) := by sorry
