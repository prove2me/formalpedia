-- Prove2me | Theorems.Thm_PI_EF_mem_rect
-- name    : PI.EF.mem_rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:06.157415+00:00
-- url     : https://prove2.me/theorems/ca22a99a-c7fd-4d24-b916-cf0bf2c2795a
-- title:
--   EF: mem rect
-- statement:
--   The EF construction uses the mem rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
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

theorem PI.EF.mem_rect {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by sorry
