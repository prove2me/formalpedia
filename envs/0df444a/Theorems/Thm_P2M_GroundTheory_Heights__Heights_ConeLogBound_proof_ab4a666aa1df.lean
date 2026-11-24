-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
-- name    : P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:48.337993+00:00
-- url     : https://prove2.me/theorems/a4647a06-cd3e-4f43-a0fb-ec20cefb28cd
-- title:
--   P2 M Ground Theory Heights  Heights Cone Log Bound proof ab4a666aa1df: P2 M Ground Theory Heights  Heights Cone Log Bound proof ab4a666aa1df
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Log Bound proof ab4a666aa1df construction uses the P2 M Ground Theory Heights  Heights Cone Log Bound proof ab4a666aa1df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L74-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L74-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLogBound».«proof» := P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
