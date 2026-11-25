-- Prove2me | Theorems.Thm_PI_WeylForUWork_denom_range
-- name    : PI.WeylForUWork.denom_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:18.719805+00:00
-- url     : https://prove2.me/theorems/798c4347-efab-5c68-aa16-d9bcdd46f659
-- title:
--   Weyl For UWork: denom range
-- statement:
--   The Weyl For UWork construction uses the denom range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaUnitary/NatWCastReal.lean#L10-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaUnitary/NatWCastReal.lean#L10-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions

theorem PI.WeylForUWork.denom_range (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by sorry
