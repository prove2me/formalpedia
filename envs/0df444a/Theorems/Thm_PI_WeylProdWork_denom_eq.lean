-- Prove2me | Theorems.Thm_PI_WeylProdWork_denom_eq
-- name    : PI.WeylProdWork.denom_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:56.490625+00:00
-- url     : https://prove2.me/theorems/ef98281c-65cc-5e85-975c-e8d2ed2f9db0
-- title:
--   Weyl Prod Work: denom eq
-- statement:
--   The Weyl Prod Work construction uses the denom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylProduct/WeylProd.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylProduct/WeylProd.lean#L11-L23

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

theorem PI.WeylProdWork.denom_eq (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by sorry
