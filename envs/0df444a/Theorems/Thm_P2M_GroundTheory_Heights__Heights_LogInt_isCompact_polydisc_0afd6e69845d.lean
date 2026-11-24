-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:05.239562+00:00
-- url     : https://prove2.me/theorems/9a13bb4e-00f9-4f4b-8f2a-ce62909e412b
-- title:
--   P2 M Ground Theory Heights  Heights Log Int is Compact polydisc 0afd6e69845d: P2 M Ground Theory Heights  Heights Log Int is Compact polydisc 0afd6e69845d
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int is Compact polydisc 0afd6e69845d construction uses the P2 M Ground Theory Heights  Heights Log Int is Compact polydisc 0afd6e69845d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L109-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d (r : ℝ) : IsCompact (polydisc ι r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«isCompact_polydisc» := P2M_GroundTheory_Heights__Heights_LogInt_isCompact_polydisc_0afd6e69845d
