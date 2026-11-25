-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:44.499076+00:00
-- url     : https://prove2.me/theorems/3ab0e961-2b04-4231-954f-c4e613037cf7
-- title:
--   P2 M Ground Theory Heights  Heights Point Line irreducible pairing 1c55fbb0a974: P2 M Ground Theory Heights  Heights Point Line irreducible pairing 1c55fbb0a974
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line irreducible pairing 1c55fbb0a974 construction uses the P2 M Ground Theory Heights  Heights Point Line irreducible pairing 1c55fbb0a974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L90-L98

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

theorem P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974 {y : Fin n → ℂ} (hy : y ≠ 0) : Irreducible (pairing y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«irreducible_pairing» := P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974
