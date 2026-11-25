-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_add_left
-- name    : PI.UnitaryGroupMassFormula.HermConj.IsHermForm.add_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:17.510587+00:00
-- url     : https://prove2.me/theorems/2fc12a6b-168f-4785-9631-a3ad628ff549
-- title:
--   Is Herm Form: add left
-- statement:
--   The Is Herm Form construction uses the add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L20-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermConj
open Matrix
variable {E : Type} [Field E]
variable {σ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] {h : V → V → E}

theorem PI.UnitaryGroupMassFormula.HermConj.IsHermForm.add_left (hh : IsHermForm σ h) (x y z : V) :
    h (x + y) z = h x z + h y z := by sorry
