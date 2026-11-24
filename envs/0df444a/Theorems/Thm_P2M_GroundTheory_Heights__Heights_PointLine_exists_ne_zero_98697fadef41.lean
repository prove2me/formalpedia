-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:55.156305+00:00
-- url     : https://prove2.me/theorems/3c693184-046e-4c2b-9893-123fed0d44ec
-- title:
--   P2 M Ground Theory Heights  Heights Point Line exists ne zero 98697fadef41: P2 M Ground Theory Heights  Heights Point Line exists ne zero 98697fadef41
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line exists ne zero 98697fadef41 construction uses the P2 M Ground Theory Heights  Heights Point Line exists ne zero 98697fadef41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41 {y : Fin n → ℂ} (hy : y ≠ 0) : ∃ a, y a ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«exists_ne_zero» := P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41
