-- Prove2me | Theorems.Thm_PI_EF_completed_ne_zero_right
-- name    : PI.EF.completed_ne_zero_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:08.752922+00:00
-- url     : https://prove2.me/theorems/fa4e339a-ff1f-55dc-8711-35c45cc6e6d2
-- title:
--   EF: completed ne zero right
-- statement:
--   The EF construction uses the completed ne zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L40-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.completed_ne_zero_right (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : completedLFunction χ s ≠ 0 := by sorry
