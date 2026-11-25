-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_hv_tri
-- name    : PI.IsoInvMetricW.hv_tri
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:36.517279+00:00
-- url     : https://prove2.me/theorems/65ff8586-25e0-4e1c-9221-907fc277f1e3
-- title:
--   Iso Inv Metric W: hv tri
-- statement:
--   The Iso Inv Metric W construction uses the hv tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L41-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L41-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric

theorem PI.IsoInvMetricW.hv_tri {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0)
    (J : ColChoice N nu) :
    hvC N nu w J = if (∀ s c i, (J s c i : ℕ) = i) then
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i else 0 := by sorry
