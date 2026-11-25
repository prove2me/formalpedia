-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_eq_zero_of_diag
-- name    : PI.UnitaryGroupMassFormula.HermConj.IsHermForm.eq_zero_of_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:01.162846+00:00
-- url     : https://prove2.me/theorems/456001d7-fb65-4a0c-a7e8-737ab5e4cc63
-- title:
--   Is Herm Form: eq zero of diag
-- statement:
--   The Is Herm Form construction uses the eq zero of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean#L28-L52

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

theorem PI.UnitaryGroupMassFormula.HermConj.IsHermForm.eq_zero_of_diag [CharZero E] (hh : IsHermForm σ h)
    (hz : ∀ x, h x x = 0) (x y : V) : h x y = 0 := by sorry
