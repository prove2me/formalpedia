-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_span_facts
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.span_facts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:33:11.01213+00:00
-- url     : https://prove2.me/theorems/afcdab95-1f76-5055-bc1d-6d5f9152a0f8
-- title:
--   Unitary Group Mass Formula: span facts
-- statement:
--   The Unitary Group Mass Formula construction uses the span facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L61-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L61-L76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
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
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG

theorem PI.NMeasInv.UnitaryGroupMassFormula.span_facts (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    (∀ b : Fin r, k ≤ b.val → hJ ε (f b) v = 0) ∧ (∀ b, hJ ε (e b) v = 0) ∧ Pw ε e f v = 0 := by sorry
