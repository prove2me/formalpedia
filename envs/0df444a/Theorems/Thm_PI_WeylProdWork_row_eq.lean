-- Prove2me | Theorems.Thm_PI_WeylProdWork_row_eq
-- name    : PI.WeylProdWork.row_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:17.760958+00:00
-- url     : https://prove2.me/theorems/a334b107-74e8-443a-9115-43fc96fc343f
-- title:
--   Weyl Prod Work: row eq
-- statement:
--   The Weyl Prod Work construction uses the row eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylProduct/WeylProd.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylProduct/WeylProd.lean#L25-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylProduct_WeylProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WeylProdWork
open Finset

theorem PI.WeylProdWork.row_eq (x : ℕ → ℝ) (n i : ℕ) :
    ∏ j ∈ range n, wg x i j =
      (∏ j ∈ Ico (i + 1) n, (x i - x j)) / ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) := by sorry
