-- Prove2me | Theorems.Thm_PI_Tr_factor_le
-- name    : PI.Tr.factor_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:41.437804+00:00
-- url     : https://prove2.me/theorems/47a3a463-5c77-5ef1-9f04-be98fde4ad81
-- title:
--   Tr: factor le
-- statement:
--   The Tr construction uses the factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/NumericMain.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/NumericMain.lean#L37-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_GaussAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_NumericMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
open PI PI.Tr

theorem PI.Tr.factor_le (κ τ m : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) (hh : τ⁻¹ * Real.exp (-κ) ≤ 1) :
    Real.exp (-κ * m) * τ ^ (-m) ≤ τ⁻¹ * Real.exp (-κ) := by sorry
