-- Prove2me | Theorems.Thm_PI_BeDiagZp_power_series_diagonal_linear
-- name    : PI.BeDiagZp.power_series_diagonal_linear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:44.033804+00:00
-- url     : https://prove2.me/theorems/f94d051c-da23-48c7-9bd5-13c00bde6937
-- title:
--   Be Diag Zp: power series diagonal linear
-- statement:
--   The Be Diag Zp construction uses the power series diagonal linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L168-L176

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
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
open SubstW

theorem PI.BeDiagZp.power_series_diagonal_linear : S1 := by sorry
