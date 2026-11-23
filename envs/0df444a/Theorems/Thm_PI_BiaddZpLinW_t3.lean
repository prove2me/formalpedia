-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_t3
-- name    : PI.BiaddZpLinW.t3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:09.666406+00:00
-- url     : https://prove2.me/theorems/986b9bb9-9395-400c-8098-7536595b8206
-- title:
--   Biadd Zp Lin W: t3
-- statement:
--   The Biadd Zp Lin W construction uses the t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L43-L56

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

theorem PI.BiaddZpLinW.t3 : ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (add l ex a b) = 0 ∧
      (∀ c, MvPowerSeries.constantCoeff (mulBy l ex c a) = 0) ∧
      add l ex a b = add l ex b a ∧
      add l ex a a = mulBy l ex 2 a ∧
      (∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a) ∧
      (∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a) ∧
      mulBy l ex 1 a = a ∧
      mulBy l ex 0 a = 0 := by sorry
