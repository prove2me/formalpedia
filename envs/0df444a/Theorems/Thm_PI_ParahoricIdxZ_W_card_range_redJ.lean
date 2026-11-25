-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_card_range_redJ
-- name    : PI.ParahoricIdxZ.W.card_range_redJ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:18.473173+00:00
-- url     : https://prove2.me/theorems/e9dce92d-5c13-4ef0-b700-0a8f059839a6
-- title:
--   W: card range red J
-- statement:
--   The W construction uses the card range red J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L18-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

theorem PI.ParahoricIdxZ.W.card_range_redJ (hϖ0 : ϖ ≠ 0) {a : ℕ} (J' : Subgroup (GL (Fin a) F))
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Nat.card (redJ O ϖ hϖ J' hJ).range = Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') := by sorry
