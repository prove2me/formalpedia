-- Prove2me | Theorems.Thm_P2M_PI_BiaddZpLinW_zc_continuous__35dffd8172ad
-- name    : P2M_PI_BiaddZpLinW_zc_continuous__35dffd8172ad
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:37.293345+00:00
-- url     : https://prove2.me/theorems/23107d22-d114-4ef0-8197-1031e59ce2ab
-- title:
--   P2 M PI Biadd Zp Lin W zc continuous  35dffd8172ad: P2 M PI Biadd Zp Lin W zc continuous  35dffd8172ad
-- statement:
--   The P2 M PI Biadd Zp Lin W zc continuous  35dffd8172ad construction uses the P2 M PI Biadd Zp Lin W zc continuous  35dffd8172ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/BiadditiveContinuousPadic.lean#L23-L25

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

theorem P2M_PI_BiaddZpLinW_zc_continuous__35dffd8172ad : Continuous (zc : ℤ_[p] → ℂ_[p]) := by sorry

alias «PI».«BiaddZpLinW».«zc_continuous'» := P2M_PI_BiaddZpLinW_zc_continuous__35dffd8172ad
