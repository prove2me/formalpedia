-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_fix
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:59.392784+00:00
-- url     : https://prove2.me/theorems/6d9a0d59-51a6-4863-84a1-bc044c19f74d
-- title:
--   SW: d S conj fix
-- statement:
--   The SW construction uses the d S conj fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L118-L126

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_fix {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hg : g i j = if i = j then 1 else 0) :
    (dS k r s * g * dS k r s⁻¹) i j = if i = j then 1 else 0 := by sorry
