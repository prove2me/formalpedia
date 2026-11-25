-- Prove2me | Theorems.Thm_PI_KoszulExact_Dc_smul
-- name    : PI.KoszulExact.Dc_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:32.285118+00:00
-- url     : https://prove2.me/theorems/8fd0ef93-4696-5d8c-9b46-881a41360374
-- title:
--   Koszul Exact: Dc smul
-- statement:
--   The Koszul Exact construction uses the Dc smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L27-L31

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

theorem PI.KoszulExact.Dc_smul (i : Fin D) (p q : ℕ) (r : R) (x : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) : Dc R i p q (r • x) := by sorry
