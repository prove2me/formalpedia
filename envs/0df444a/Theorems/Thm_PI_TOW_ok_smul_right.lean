-- Prove2me | Theorems.Thm_PI_TOW_ok_smul_right
-- name    : PI.TOW.ok_smul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:52.196358+00:00
-- url     : https://prove2.me/theorems/1dcf0ae4-a821-44ce-9daf-5b15d4fd1d5a
-- title:
--   TOW: ok smul right
-- statement:
--   The TOW construction uses the ok smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/OkSmulRight.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/OkSmulRight.lean#L51-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}

theorem PI.TOW.ok_smul_right (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c β (a • s) := by sorry
