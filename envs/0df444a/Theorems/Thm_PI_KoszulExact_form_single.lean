-- Prove2me | Theorems.Thm_PI_KoszulExact_form_single
-- name    : PI.KoszulExact.form_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:46:31.322098+00:00
-- url     : https://prove2.me/theorems/93bd7936-492e-5f7f-95a4-54dea61a8923
-- title:
--   Koszul Exact: form single
-- statement:
--   The Koszul Exact construction uses the form single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L46-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}

theorem PI.KoszulExact.form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by sorry
