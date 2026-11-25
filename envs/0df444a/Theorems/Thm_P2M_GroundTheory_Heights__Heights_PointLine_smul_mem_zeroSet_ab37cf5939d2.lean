-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:20.498811+00:00
-- url     : https://prove2.me/theorems/5cbf55ac-cda8-405f-b053-dc1d68fe3e35
-- title:
--   P2 M Ground Theory Heights  Heights Point Line smul mem zero Set ab37cf5939d2: P2 M Ground Theory Heights  Heights Point Line smul mem zero Set ab37cf5939d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line smul mem zero Set ab37cf5939d2 construction uses the P2 M Ground Theory Heights  Heights Point Line smul mem zero Set ab37cf5939d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L41-L46

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

theorem P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2 {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«smul_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2
