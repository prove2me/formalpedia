-- Prove2me | Theorems.Thm_PI_BiaddZpLinW_t0
-- name    : PI.BiaddZpLinW.t0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:35.51255+00:00
-- url     : https://prove2.me/theorems/2df18107-1b86-441d-b3d1-58fe1b2b0400
-- title:
--   Biadd Zp Lin W: t0
-- statement:
--   The Biadd Zp Lin W construction uses the t0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiaddZpLinOf.lean#L15-L18

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

theorem PI.BiaddZpLinW.t0 : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h f' g' : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq f' g' → Simeq (f + f') (g + g')) := by sorry
