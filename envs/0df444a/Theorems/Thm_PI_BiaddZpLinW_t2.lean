-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_t2
-- name    : PI.BiaddZpLinW.t2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:46.975352+00:00
-- url     : https://prove2.me/theorems/cff56aa0-5bca-4ee4-872f-54c1f79f8568
-- title:
--   Biadd Zp Lin W: t2
-- statement:
--   The Biadd Zp Lin W construction uses the t2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L26-L41

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

theorem PI.BiaddZpLinW.t2 : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    ∀ (σ τ : Type) [Finite σ] (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i) ∧
    (∀ (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.subst s (MvPowerSeries.C c * a) = MvPowerSeries.C c * MvPowerSeries.subst s a) ∧
    (∀ a b : MvPowerSeries σ ℂ_[p],
      MvPowerSeries.subst s (a + b) = MvPowerSeries.subst s a + MvPowerSeries.subst s b) ∧
    ∀ a b : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 ∧
      MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) ∧
      (∀ c, MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a)) ∧
      MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) ∧
      MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by sorry
