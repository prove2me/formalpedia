-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_inner_bounds
-- name    : PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:12.683833+00:00
-- url     : https://prove2.me/theorems/f66b7140-5d9e-52da-8589-bb7e373a9106
-- title:
--   Index UBound: inner bounds
-- statement:
--   The Index UBound construction uses the inner bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L40-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L40-L67

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

theorem PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds (g : ℝ) (hg : 2 ≤ g) (r : ℕ) :
    0 ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ∧ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ≤ 1 ∧
      1 - 1 / (g - 1) ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by sorry
