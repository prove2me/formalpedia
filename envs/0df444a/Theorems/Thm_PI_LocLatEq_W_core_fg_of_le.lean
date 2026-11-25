-- Prove2me | Theorems.Thm_PI_LocLatEq_W_core_fg_of_le
-- name    : PI.LocLatEq.W.core_fg_of_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:14:03.489597+00:00
-- url     : https://prove2.me/theorems/27cb10fb-4676-4531-90b1-e339fe5af62e
-- title:
--   W: core fg of le
-- statement:
--   The W construction uses the core fg of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreFgOfLe.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreFgOfLe.lean#L13-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W

theorem PI.LocLatEq.W.core_fg_of_le {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M]
    [Module R M] {N P : Submodule R M} (hN : N.FG) (h : P ≤ N) : P.FG := by sorry
