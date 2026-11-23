-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_mul_dS_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:40.42481+00:00
-- url     : https://prove2.me/theorems/88ba290f-ea23-4c98-bfcc-fd97b5605890
-- title:
--   SW: d S mul d S inv
-- statement:
--   The SW construction uses the d S mul d S inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean#L97-L101

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_mul_dS_inv {s : ℝ} (hs : s ≠ 0) : dS k r s * dS k r s⁻¹ = 1 := by sorry
