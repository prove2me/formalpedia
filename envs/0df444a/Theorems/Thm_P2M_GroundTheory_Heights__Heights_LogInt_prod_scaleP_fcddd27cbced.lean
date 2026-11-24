-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:28.746267+00:00
-- url     : https://prove2.me/theorems/2eb1c720-3ab8-4f83-a55a-0d0ffc895bd2
-- title:
--   P2 M Ground Theory Heights  Heights Log Int prod scale P fcddd27cbced: P2 M Ground Theory Heights  Heights Log Int prod scale P fcddd27cbced
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int prod scale P fcddd27cbced construction uses the P2 M Ground Theory Heights  Heights Log Int prod scale P fcddd27cbced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) (m : ι →₀ ℕ) :
    ∏ i ∈ m.support, scaleP p a u i ^ m i =
      a ^ Finsupp.weight (indW p) m * ∏ i ∈ m.support, u i ^ m i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«prod_scaleP» := P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced
