-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:18.819235+00:00
-- url     : https://prove2.me/theorems/2c1af677-88c8-4933-bf34-ce1ea377ef87
-- title:
--   P2 M Ground Theory Heights  Heights Log Int ae eval ne zero e1e014cbbf7d: P2 M Ground Theory Heights  Heights Log Int ae eval ne zero e1e014cbbf7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int ae eval ne zero e1e014cbbf7d construction uses the P2 M Ground Theory Heights  Heights Log Int ae eval ne zero e1e014cbbf7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L282-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L282-L285

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) (r : ℝ) :
    ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«ae_eval_ne_zero» := P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
