-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DefectPoint_proof_a283805ec7d4
-- name    : P2M_GroundTheory_Heights__Heights_DefectPoint_proof_a283805ec7d4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:23.279819+00:00
-- url     : https://prove2.me/theorems/10855627-b877-47fb-b6cc-ecbc7d7a4de1
-- title:
--   P2 M Ground Theory Heights  Heights Defect Point proof a283805ec7d4: P2 M Ground Theory Heights  Heights Defect Point proof a283805ec7d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Defect Point proof a283805ec7d4 construction uses the P2 M Ground Theory Heights  Heights Defect Point proof a283805ec7d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectPoint.lean#L32-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDefectPoint.lean#L32-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_DefectPoint_proof_a283805ec7d4 (h1 : PointLine.Statement) (h2 : PointChowForm.Statement)
    (h3 : ConeIntegralLine.Statement) (h4 : FsLogSmul.Statement) (h5 : ConeIntegralMass.Statement) :
    DefectPoint.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DefectPoint».«proof» := P2M_GroundTheory_Heights__Heights_DefectPoint_proof_a283805ec7d4
