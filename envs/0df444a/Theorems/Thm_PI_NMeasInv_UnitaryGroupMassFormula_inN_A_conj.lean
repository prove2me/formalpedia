-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_inN_A_conj
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.inN_A_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:04.543806+00:00
-- url     : https://prove2.me/theorems/c14f6aa3-0d57-4027-91cb-7d5a952972dc
-- title:
--   Unitary Group Mass Formula: in N A conj
-- statement:
--   The Unitary Group Mass Formula construction uses the in N A conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L235-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L235-L256

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.inN_A_conj (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) {z : Fin n → ℂ} (hez : ∀ a, hJ ε (e a) z = 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) :
    InN ε e z (Amat ε e f s * g * Amat ε e f s⁻¹) := by sorry
