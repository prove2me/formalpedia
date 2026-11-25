-- Prove2me | Theorems.Thm_P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1
-- name    : P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:01:22.991745+00:00
-- url     : https://prove2.me/theorems/bd504b23-09fa-56b8-a08f-2a5aa9fe61f0
-- title:
--   P2 M PI WFJM Shape pos of  N cf6537b449c1: P2 M PI WFJM Shape pos of  N cf6537b449c1
-- statement:
--   The P2 M PI WFJM Shape pos of  N cf6537b449c1 construction uses the P2 M PI WFJM Shape pos of  N cf6537b449c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L175-L183

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

theorem P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1 (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin (nN f)) : 0 < αN f i := by sorry

alias «PI».«WFJM».«Shape».«pos_of_αN» := P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1
