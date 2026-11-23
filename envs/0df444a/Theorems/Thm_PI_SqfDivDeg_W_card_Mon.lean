-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_card_Mon
-- name    : PI.SqfDivDeg.W.card_Mon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:54.813256+00:00
-- url     : https://prove2.me/theorems/76e9a668-35da-4d16-9221-36f80d53d150
-- title:
--   W: card Mon
-- statement:
--   The W construction uses the card Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/MonicFintype.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/MonicFintype.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfLab
import Definitions.Def_Formalism_PeriodIntegrals_SqfDivDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W

theorem PI.SqfDivDeg.W.card_Mon (g : ℕ) [Fact g.Prime] (n : ℕ) : (Mon g n).card = g ^ n := by sorry
