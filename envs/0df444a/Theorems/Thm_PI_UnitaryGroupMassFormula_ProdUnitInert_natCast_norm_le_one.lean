-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_natCast_norm_le_one
-- name    : PI.UnitaryGroupMassFormula.ProdUnitInert.natCast_norm_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:00.866099+00:00
-- url     : https://prove2.me/theorems/e070c3f6-1975-4426-8288-ac62473941ae
-- title:
--   Prod Unit Inert: nat Cast norm le one
-- statement:
--   The Prod Unit Inert construction uses the nat Cast norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]

theorem PI.UnitaryGroupMassFormula.ProdUnitInert.natCast_norm_le_one (d : ℕ) : ‖(d : ℚ_[p])‖ ≤ 1 := by sorry
