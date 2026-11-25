-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_eval_smul_of_isHomogeneous_b8676a5b40e2
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_eval_smul_of_isHomogeneous_b8676a5b40e2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:34.293284+00:00
-- url     : https://prove2.me/theorems/392f62bf-3735-464b-9ac0-772951bb15c0
-- title:
--   P2 M Ground Theory Heights  Heights Point Line eval smul of is Homogeneous b8676a5b40e2: P2 M Ground Theory Heights  Heights Point Line eval smul of is Homogeneous b8676a5b40e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line eval smul of is Homogeneous b8676a5b40e2 construction uses the P2 M Ground Theory Heights  Heights Point Line eval smul of is Homogeneous b8676a5b40e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L32-L39

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

theorem P2M_GroundTheory_Heights__Heights_PointLine_eval_smul_of_isHomogeneous_b8676a5b40e2 {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«eval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_PointLine_eval_smul_of_isHomogeneous_b8676a5b40e2
