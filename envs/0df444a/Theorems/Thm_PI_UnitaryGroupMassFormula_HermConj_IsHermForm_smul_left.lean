-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_smul_left
-- name    : PI.UnitaryGroupMassFormula.HermConj.IsHermForm.smul_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:21.791458+00:00
-- url     : https://prove2.me/theorems/0ef94701-381c-4174-a09e-4b64ba9917c6
-- title:
--   Is Herm Form: smul left
-- statement:
--   The Is Herm Form construction uses the smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L24-L26

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

theorem PI.UnitaryGroupMassFormula.HermConj.IsHermForm.smul_left (hh : IsHermForm σ h) (a : E) (x y : V) :
    h (a • x) y = σ a * h x y := by sorry
