-- Prove2me | Theorems.Thm_P2M_PI_TrDualLocW_isIntegral_natCast__ed679ab41ce3
-- name    : P2M_PI_TrDualLocW_isIntegral_natCast__ed679ab41ce3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:32.899831+00:00
-- url     : https://prove2.me/theorems/ceed2f18-f3fd-532b-98bd-2b56662fca8f
-- title:
--   P2 M PI Tr Dual Loc W is Integral nat Cast  ed679ab41ce3: P2 M PI Tr Dual Loc W is Integral nat Cast  ed679ab41ce3
-- statement:
--   The P2 M PI Tr Dual Loc W is Integral nat Cast  ed679ab41ce3 construction uses the P2 M PI Tr Dual Loc W is Integral nat Cast  ed679ab41ce3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralNatCast.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralNatCast.lean#L12-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]

theorem P2M_PI_TrDualLocW_isIntegral_natCast__ed679ab41ce3 (n : ℕ) : IsIntegral ℤ (n : K) := by sorry

alias «PI».«TrDualLocW».«isIntegral_natCast'» := P2M_PI_TrDualLocW_isIntegral_natCast__ed679ab41ce3
