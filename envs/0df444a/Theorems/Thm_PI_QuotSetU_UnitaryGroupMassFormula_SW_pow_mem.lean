-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_pow_mem
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:21.649003+00:00
-- url     : https://prove2.me/theorems/18d37980-1fcb-4c79-8f7b-7182e771f27d
-- title:
--   SW: pow mem
-- statement:
--   The SW construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsCompactInterUnitBox.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsCompactInterUnitBox.lean#L26-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
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
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.pow_mem (hG : IsMatGroup G) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G) (n : ℕ) : x ^ n ∈ G := by sorry
