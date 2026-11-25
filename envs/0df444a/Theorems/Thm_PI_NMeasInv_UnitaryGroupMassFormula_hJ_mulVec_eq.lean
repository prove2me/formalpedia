-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_mulVec_eq
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.hJ_mulVec_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:53.240351+00:00
-- url     : https://prove2.me/theorems/45a721b7-264e-48dc-a5b6-950c026b7e65
-- title:
--   Unitary Group Mass Formula: h J mul Vec eq
-- statement:
--   The Unitary Group Mass Formula construction uses the h J mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L201-L205

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.hJ_mulVec_eq (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = star x ⬝ᵥ ((Mᴴ * Formalism.REAL.Jm ε * M) *ᵥ y) := by sorry
