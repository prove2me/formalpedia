-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:34.417603+00:00
-- url     : https://prove2.me/theorems/00ebda2b-decf-4406-a2b1-c50ed0d9a9b0
-- title:
--   P2 M Ground Theory Heights  Heights Point Line pairing dvd of vanish 9f2009f89a61: P2 M Ground Theory Heights  Heights Point Line pairing dvd of vanish 9f2009f89a61
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line pairing dvd of vanish 9f2009f89a61 construction uses the P2 M Ground Theory Heights  Heights Point Line pairing dvd of vanish 9f2009f89a61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L48-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L48-L88

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

theorem P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61 {y : Fin n → ℂ} (hy : y ≠ 0) (f : MvPolynomial (Fin 1 × Fin n) ℂ)
    (hf : ∀ u, eval u (pairing y) = 0 → eval u f = 0) : pairing y ∣ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«pairing_dvd_of_vanish» := P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61
