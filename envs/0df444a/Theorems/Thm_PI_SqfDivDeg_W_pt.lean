-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_pt
-- name    : PI.SqfDivDeg.W.pt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:46.03985+00:00
-- url     : https://prove2.me/theorems/54b75d6f-fe08-5e29-b3d6-3e99a64a230e
-- title:
--   W: pt
-- statement:
--   The W construction uses the pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L81-L91

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical

theorem PI.SqfDivDeg.W.pt (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by sorry
