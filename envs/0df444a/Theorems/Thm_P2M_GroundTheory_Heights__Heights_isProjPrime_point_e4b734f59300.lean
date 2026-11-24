-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
-- name    : P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:10.224804+00:00
-- url     : https://prove2.me/theorems/f40cdb49-7889-4aa0-b3f9-00bf82e3124f
-- title:
--   P2 M Ground Theory Heights  Heights is Proj Prime point e4b734f59300: P2 M Ground Theory Heights  Heights is Proj Prime point e4b734f59300
-- statement:
--   The P2 M Ground Theory Heights  Heights is Proj Prime point e4b734f59300 construction uses the P2 M Ground Theory Heights  Heights is Proj Prime point e4b734f59300 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L310-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L310-L316

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300 (F : Type*) [Field F] :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) F)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isProjPrime_point» := P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
