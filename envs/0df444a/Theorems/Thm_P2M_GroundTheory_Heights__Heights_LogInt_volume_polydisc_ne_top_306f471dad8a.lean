-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:29.081643+00:00
-- url     : https://prove2.me/theorems/1cb8caaf-996f-4db5-9b77-cac5f12fa5e6
-- title:
--   P2 M Ground Theory Heights  Heights Log Int volume polydisc ne top 306f471dad8a: P2 M Ground Theory Heights  Heights Log Int volume polydisc ne top 306f471dad8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int volume polydisc ne top 306f471dad8a construction uses the P2 M Ground Theory Heights  Heights Log Int volume polydisc ne top 306f471dad8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L112-L113

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a [Fintype ι] (r : ℝ) : volume (polydisc ι r) ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«volume_polydisc_ne_top» := P2M_GroundTheory_Heights__Heights_LogInt_volume_polydisc_ne_top_306f471dad8a
