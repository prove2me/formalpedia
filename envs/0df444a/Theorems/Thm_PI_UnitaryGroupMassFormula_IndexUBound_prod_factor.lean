-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_prod_factor
-- name    : PI.UnitaryGroupMassFormula.IndexUBound.prod_factor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:35.448502+00:00
-- url     : https://prove2.me/theorems/e260effb-7139-4c54-adcb-ce8aa065326b
-- title:
--   Index UBound: prod factor
-- statement:
--   The Index UBound construction uses the prod factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L34-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset

theorem PI.UnitaryGroupMassFormula.IndexUBound.prod_factor (g : ℝ) (hg : g ≠ 0) (r : ℕ) :
    ∏ i ∈ Ico 1 r, (g ^ i - 1) = g ^ (r * (r - 1) / 2) * ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by sorry
