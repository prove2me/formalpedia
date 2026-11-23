-- Prove2me | Theorems.Thm_PI_EF_sum_mult_le_of_subset
-- name    : PI.EF.sum_mult_le_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:00.059918+00:00
-- url     : https://prove2.me/theorems/eae3285b-6597-4284-bd6f-d80743b0b280
-- title:
--   EF: sum mult le of subset
-- statement:
--   The EF construction uses the sum mult le of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L105-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L105-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
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
open DirichletCharacter

theorem PI.EF.sum_mult_le_of_subset {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t1 t2 : ℝ}
    (h1 : (ZerosNear χ t1).Finite) (h2 : (ZerosNear χ t2).Finite) (B : Finset ℂ)
    (hB : (B : Set ℂ) ⊆ ZerosNear χ t1 ∪ ZerosNear χ t2) :
    ∑ ρ ∈ B, (mult χ ρ : ℝ) ≤ wsum χ t1 + wsum χ t2 := by sorry
