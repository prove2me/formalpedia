-- Prove2me | Theorems.Thm_P2M_PI_BiaddZpLinW_zc_natCast__19adea702169
-- name    : P2M_PI_BiaddZpLinW_zc_natCast__19adea702169
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:41.7115+00:00
-- url     : https://prove2.me/theorems/4dea04ad-fb54-4ff7-95bb-e21bc464dbd6
-- title:
--   P2 M PI Biadd Zp Lin W zc nat Cast  19adea702169: P2 M PI Biadd Zp Lin W zc nat Cast  19adea702169
-- statement:
--   The P2 M PI Biadd Zp Lin W zc nat Cast  19adea702169 construction uses the P2 M PI Biadd Zp Lin W zc nat Cast  19adea702169 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L27-L28

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

theorem P2M_PI_BiaddZpLinW_zc_natCast__19adea702169 (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by sorry

alias «PI».«BiaddZpLinW».«zc_natCast'» := P2M_PI_BiaddZpLinW_zc_natCast__19adea702169
