-- Prove2me | Theorems.Thm_PI_KoszulExact_Dc_add
-- name    : PI.KoszulExact.Dc_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:39.45106+00:00
-- url     : https://prove2.me/theorems/f624c02a-cda5-49ff-ac10-6cf80c68cb70
-- title:
--   Koszul Exact: Dc add
-- statement:
--   The Koszul Exact construction uses the Dc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L19-L25

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

theorem PI.KoszulExact.Dc_add (i : Fin D) (p q : ℕ) (x y : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) (hy : Dc R i p q y) : Dc R i p q (x + y) := by sorry
