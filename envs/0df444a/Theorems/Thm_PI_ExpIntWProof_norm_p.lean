-- Prove2me | Theorems.Thm_PI_ExpIntWProof_norm_p
-- name    : PI.ExpIntWProof.norm_p
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:14.57241+00:00
-- url     : https://prove2.me/theorems/4ddcd127-5fda-4f47-a62e-8e560b8e8b82
-- title:
--   Exp Int WProof: norm p
-- statement:
--   The Exp Int WProof construction uses the norm p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L9-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI

theorem PI.ExpIntWProof.norm_p (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by sorry
