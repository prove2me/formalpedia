-- Prove2me | Theorems.Thm_PI_KoszulExact_one_mem_pow_zero
-- name    : PI.KoszulExact.one_mem_pow_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:46.175821+00:00
-- url     : https://prove2.me/theorems/b03fb8c1-0267-56b0-be75-39cc650e552b
-- title:
--   Koszul Exact: one mem pow zero
-- statement:
--   The Koszul Exact construction uses the one mem pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L42-L44

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

theorem PI.KoszulExact.one_mem_pow_zero (i : ℕ) : (1 : ExteriorAlgebra R (Fin D → R)) ∈ Li R D i ^ 0 := by sorry
