-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:46.289916+00:00
-- url     : https://prove2.me/theorems/3bd421d0-bb94-44fd-be39-64726afc2319
-- title:
--   P2 M Ground Theory Heights  Heights Point Line eval pairing f70de561052b: P2 M Ground Theory Heights  Heights Point Line eval pairing f70de561052b
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line eval pairing f70de561052b construction uses the P2 M Ground Theory Heights  Heights Point Line eval pairing f70de561052b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b (y : Fin n → ℂ) (u : Fin 1 × Fin n → ℂ) :
    eval u (pairing y) = ∑ j, y j * u (0, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«eval_pairing» := P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b
