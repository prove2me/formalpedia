-- Prove2me | Theorems.Thm_PI_KoszulExact_eb_mul_self
-- name    : PI.KoszulExact.eb_mul_self
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:19.943862+00:00
-- url     : https://prove2.me/theorems/422805f2-ad59-43c3-9074-c3ce8215bd44
-- title:
--   Koszul Exact: eb mul self
-- statement:
--   The Koszul Exact construction uses the eb mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L36-L37

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

theorem PI.KoszulExact.eb_mul_self (i : Fin D) : eb R i * eb R i = 0 := by sorry
