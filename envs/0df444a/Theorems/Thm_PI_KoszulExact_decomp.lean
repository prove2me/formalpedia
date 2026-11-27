-- Prove2me | Theorems.Thm_PI_KoszulExact_decomp
-- name    : PI.KoszulExact.decomp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:46:25.621198+00:00
-- url     : https://prove2.me/theorems/1fcdaaad-63a6-514b-aedd-d210fb99d2ad
-- title:
--   Koszul Exact: decomp
-- statement:
--   The Koszul Exact construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L46-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L46-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}

theorem PI.KoszulExact.decomp (i : Fin D) : ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)),
    x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b := by sorry
