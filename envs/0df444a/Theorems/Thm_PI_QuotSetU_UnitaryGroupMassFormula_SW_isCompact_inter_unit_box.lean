-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isCompact_inter_unit_box
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.isCompact_inter_unit_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:28.6678+00:00
-- url     : https://prove2.me/theorems/f42fcedd-1e26-4129-96d7-22cb886f79a5
-- title:
--   SW: is Compact inter unit box
-- statement:
--   The SW construction uses the is Compact inter unit box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsCompactInterUnitBox.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsCompactInterUnitBox.lean#L58-L77

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.isCompact_inter_unit_box (hG : IsClosed G) : IsCompact (G ∩ box1 m) := by sorry
