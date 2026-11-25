-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_S_iff
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_S_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:09.46523+00:00
-- url     : https://prove2.me/theorems/bd929eae-2261-44c7-83af-652ea2d90bf0
-- title:
--   SW: d S conj S iff
-- statement:
--   The SW construction uses the d S conj S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L156-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L156-L170

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_S_iff {s : ℝ} (hs : s ≠ 0) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by sorry
