-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_inUJ_of_hJ
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.inUJ_of_hJ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:13:59.895353+00:00
-- url     : https://prove2.me/theorems/33afcb87-e4ab-408b-b0a4-d8e2fd8ae6b7
-- title:
--   Unitary Group Mass Formula: in UJ of h J
-- statement:
--   The Unitary Group Mass Formula construction uses the in UJ of h J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L208-L215

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
omit hG

theorem PI.NMeasInv.UnitaryGroupMassFormula.inUJ_of_hJ (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε M := by sorry
