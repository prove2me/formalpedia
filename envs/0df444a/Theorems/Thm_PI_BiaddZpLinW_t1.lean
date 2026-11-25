-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_t1
-- name    : PI.BiaddZpLinW.t1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:28.743591+00:00
-- url     : https://prove2.me/theorems/1e8d85ff-14b2-482e-8dc0-b56e60312bdd
-- title:
--   Biadd Zp Lin W: t1
-- statement:
--   The Biadd Zp Lin W construction uses the t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L20-L24

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

theorem PI.BiaddZpLinW.t1 : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f g : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f g → Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) := by sorry
