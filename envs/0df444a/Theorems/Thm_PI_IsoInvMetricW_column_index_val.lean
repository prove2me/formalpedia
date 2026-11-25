-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_column_index_val
-- name    : PI.IsoInvMetricW.column_index_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:32.72786+00:00
-- url     : https://prove2.me/theorems/cf5b5b08-380c-44f0-a43c-eeddb0ee76de
-- title:
--   Iso Inv Metric W: column index val
-- statement:
--   The Iso Inv Metric W construction uses the column index val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L45-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem PI.IsoInvMetricW.column_index_val (hle : ∀ z, (nu z).colLen 0 ≤ N) (s : Lt) (c : Fin ((nu s).rowLen 0))
    (i : Fin ((nu s).colLen c)) : ((J0 nu hle s c i : Fin N) : ℕ) = i := by sorry
