-- Prove2me | Theorems.Thm_PI_EF_zerosBelow_finite
-- name    : PI.EF.zerosBelow_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:19.417977+00:00
-- url     : https://prove2.me/theorems/71d45ab9-f145-46d4-9b09-cf5872d5fb90
-- title:
--   EF: zeros Below finite
-- statement:
--   The EF construction uses the zeros Below finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L132-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L132-L146

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
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
open DirichletCharacter

theorem PI.EF.zerosBelow_finite {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (T : ℝ) : (ZerosBelow χ T).Finite := by sorry
