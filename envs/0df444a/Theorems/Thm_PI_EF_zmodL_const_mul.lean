-- Prove2me | Theorems.Thm_PI_EF_zmodL_const_mul
-- name    : PI.EF.zmodL_const_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:19.32956+00:00
-- url     : https://prove2.me/theorems/016a0fa9-b602-46a4-a367-d54866f2c7ca
-- title:
--   EF: zmod L const mul
-- statement:
--   The EF construction uses the zmod L const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean#L13-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
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
open Complex DirichletCharacter
open scoped ZMod
variable {N : ℕ} [NeZero N]

theorem PI.EF.zmodL_const_mul (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by sorry
