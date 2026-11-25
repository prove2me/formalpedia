-- Prove2me | Theorems.Thm_PI_KoszulExact_eb_mul_swap
-- name    : PI.KoszulExact.eb_mul_swap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:54.195376+00:00
-- url     : https://prove2.me/theorems/55fd2a7d-15c9-4799-8fba-8df768571f61
-- title:
--   Koszul Exact: eb mul swap
-- statement:
--   The Koszul Exact construction uses the eb mul swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L33-L34

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

theorem PI.KoszulExact.eb_mul_swap (k i : Fin D) : eb R k * eb R i = -(eb R i * eb R k) := by sorry
