-- Prove2me | Theorems.Thm_P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165
-- name    : P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:40.960959+00:00
-- url     : https://prove2.me/theorems/07162a85-480e-452e-9fdb-24684a6d89c3
-- title:
--   P2 M PI WFJM Shape pos of  P 7e79a0d73165: P2 M PI WFJM Shape pos of  P 7e79a0d73165
-- statement:
--   The P2 M PI WFJM Shape pos of  P 7e79a0d73165 construction uses the P2 M PI WFJM Shape pos of  P 7e79a0d73165 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L167-L173

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}

theorem P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165 (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin (nP f)) : 0 < αP f i := by sorry

alias «PI».«WFJM».«Shape».«pos_of_αP» := P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165
