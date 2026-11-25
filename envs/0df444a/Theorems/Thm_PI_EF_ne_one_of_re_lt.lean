-- Prove2me | Theorems.Thm_PI_EF_ne_one_of_re_lt
-- name    : PI.EF.ne_one_of_re_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:52.182325+00:00
-- url     : https://prove2.me/theorems/6dc0699a-4a5b-5830-b323-9db8e660709e
-- title:
--   EF: ne one of re lt
-- statement:
--   The EF construction uses the ne one of re lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L90-L92

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

theorem PI.EF.ne_one_of_re_lt {ρ : ℂ} (h : ρ.re < 1) : ρ ≠ 1 := by sorry
