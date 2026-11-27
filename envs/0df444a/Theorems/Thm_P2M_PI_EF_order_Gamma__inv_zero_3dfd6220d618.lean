-- Prove2me | Theorems.Thm_P2M_PI_EF_order_Gamma__inv_zero_3dfd6220d618
-- name    : P2M_PI_EF_order_Gamma__inv_zero_3dfd6220d618
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:25.830305+00:00
-- url     : https://prove2.me/theorems/e5c0eec7-f6fe-4193-9aeb-01677de7d603
-- title:
--   P2 M PI EF order Gamma  inv zero 3dfd6220d618: P2 M PI EF order Gamma  inv zero 3dfd6220d618
-- statement:
--   The P2 M PI EF order Gamma  inv zero 3dfd6220d618 construction uses the P2 M PI EF order Gamma  inv zero 3dfd6220d618 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L141-L148

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem P2M_PI_EF_order_Gamma__inv_zero_3dfd6220d618 : analyticOrderAt (fun s : ℂ => (Gammaℝ s)⁻¹) 0 = 1 := by sorry

alias «PI».«EF».«order_Gammaℝ_inv_zero» := P2M_PI_EF_order_Gamma__inv_zero_3dfd6220d618
