-- Prove2me | Theorems.Thm_PI_EF_completed_ne_zero_left
-- name    : PI.EF.completed_ne_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:46.1138+00:00
-- url     : https://prove2.me/theorems/48f5ed44-15ca-4373-a97d-15bd4eddd13c
-- title:
--   EF: completed ne zero left
-- statement:
--   The EF construction uses the completed ne zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L51-L63

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

theorem PI.EF.completed_ne_zero_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := by sorry
