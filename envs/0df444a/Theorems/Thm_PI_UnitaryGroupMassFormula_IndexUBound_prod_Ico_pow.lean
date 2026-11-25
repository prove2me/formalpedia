-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_prod_Ico_pow
-- name    : PI.UnitaryGroupMassFormula.IndexUBound.prod_Ico_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:34.840433+00:00
-- url     : https://prove2.me/theorems/8bd83b96-44c3-47b7-ac3d-e602dd691021
-- title:
--   Index UBound: prod Ico pow
-- statement:
--   The Index UBound construction uses the prod Ico pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexUpperBound/OneSubSumLeProd.lean#L25-L32

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

theorem PI.UnitaryGroupMassFormula.IndexUBound.prod_Ico_pow (g : ℝ) (r : ℕ) :
    ∏ i ∈ Ico 1 r, g ^ i = g ^ (r * (r - 1) / 2) := by sorry
