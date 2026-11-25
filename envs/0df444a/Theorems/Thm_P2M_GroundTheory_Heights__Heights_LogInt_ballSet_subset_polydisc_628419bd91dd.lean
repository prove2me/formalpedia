-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ballSet_subset_polydisc_628419bd91dd
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_ballSet_subset_polydisc_628419bd91dd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:52.693266+00:00
-- url     : https://prove2.me/theorems/d735c17f-27f2-4618-b6ae-d9217574e7c7
-- title:
--   P2 M Ground Theory Heights  Heights Log Int ball Set subset polydisc 628419bd91dd: P2 M Ground Theory Heights  Heights Log Int ball Set subset polydisc 628419bd91dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int ball Set subset polydisc 628419bd91dd construction uses the P2 M Ground Theory Heights  Heights Log Int ball Set subset polydisc 628419bd91dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L25-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_ballSet_subset_polydisc_628419bd91dd (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«ballSet_subset_polydisc» := P2M_GroundTheory_Heights__Heights_LogInt_ballSet_subset_polydisc_628419bd91dd
