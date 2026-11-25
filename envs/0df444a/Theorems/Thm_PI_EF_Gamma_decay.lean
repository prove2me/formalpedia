-- Prove2me | Theorems.Thm_PI_EF_Gamma_decay
-- name    : PI.EF.Gamma_decay
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:09.876978+00:00
-- url     : https://prove2.me/theorems/252a8f44-8a69-48b4-8dd8-f5544be9f1e8
-- title:
--   EF: Gamma decay
-- statement:
--   The EF construction uses the Gamma decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L222-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L222-L241

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
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
open Complex Filter Set

theorem PI.EF.Gamma_decay {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) :
    ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * |w.im|) ≤ 3 * ‖w + 1‖ ^ 5 := by sorry
