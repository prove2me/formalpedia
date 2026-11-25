-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_card_GL_real
-- name    : PI.ParahoricIdxZ.W.card_GL_real
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:43.078436+00:00
-- url     : https://prove2.me/theorems/9377b310-58d4-48b0-bbca-35cd483ef55f
-- title:
--   W: card GL real
-- statement:
--   The W construction uses the card GL real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/SpanIsMaximal.lean#L38-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W

theorem PI.ParahoricIdxZ.W.card_GL_real (k : Type) [Field k] [Fintype k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Fintype.card k : ℝ) ^ (n * n) * qE (Fintype.card k) 1 n := by sorry
