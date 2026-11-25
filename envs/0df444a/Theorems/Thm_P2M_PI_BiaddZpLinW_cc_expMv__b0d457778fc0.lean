-- Prove2me | Theorems.Thm_P2M_PI_BiaddZpLinW_cc_expMv__b0d457778fc0
-- name    : P2M_PI_BiaddZpLinW_cc_expMv__b0d457778fc0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:42.941571+00:00
-- url     : https://prove2.me/theorems/735c6fe9-96f5-43b7-8f6a-39f9c0763498
-- title:
--   P2 M PI Biadd Zp Lin W cc exp Mv  b0d457778fc0: P2 M PI Biadd Zp Lin W cc exp Mv  b0d457778fc0
-- statement:
--   The P2 M PI Biadd Zp Lin W cc exp Mv  b0d457778fc0 construction uses the P2 M PI Biadd Zp Lin W cc exp Mv  b0d457778fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L16-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiadditiveContinuousPadic
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
open PI.BiaddZpLin PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_BiaddZpLinW_cc_expMv__b0d457778fc0 {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by sorry

alias «PI».«BiaddZpLinW».«cc_expMv'» := P2M_PI_BiaddZpLinW_cc_expMv__b0d457778fc0
