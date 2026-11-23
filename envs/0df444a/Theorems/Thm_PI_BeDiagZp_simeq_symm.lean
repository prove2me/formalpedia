-- Prove2me | Theorems.Thm_PI_BeDiagZp_simeq_symm
-- name    : PI.BeDiagZp.simeq_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:18.975989+00:00
-- url     : https://prove2.me/theorems/5e503fed-9fcb-4b44-ae2e-c0ae675212e5
-- title:
--   Be Diag Zp: simeq symm
-- statement:
--   The Be Diag Zp construction uses the simeq symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L174-L177

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
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
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.BeDiagZp.simeq_symm {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by sorry
