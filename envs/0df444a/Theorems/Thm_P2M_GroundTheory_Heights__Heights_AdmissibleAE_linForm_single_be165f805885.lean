-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AdmissibleAE_linForm_single_be165f805885
-- name    : P2M_GroundTheory_Heights__Heights_AdmissibleAE_linForm_single_be165f805885
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:22.562776+00:00
-- url     : https://prove2.me/theorems/13423b6e-91c7-437a-a388-b8245d1c1ddd
-- title:
--   P2 M Ground Theory Heights  Heights Admissible AE lin Form single be165f805885: P2 M Ground Theory Heights  Heights Admissible AE lin Form single be165f805885
-- statement:
--   The P2 M Ground Theory Heights  Heights Admissible AE lin Form single be165f805885 construction uses the P2 M Ground Theory Heights  Heights Admissible AE lin Form single be165f805885 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAE.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAE.lean#L31-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAE
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
open MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.AdmissibleAE
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AdmissibleAE_linForm_single_be165f805885 (j : Fin n) :
    linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AdmissibleAE».«linForm_single» := P2M_GroundTheory_Heights__Heights_AdmissibleAE_linForm_single_be165f805885
