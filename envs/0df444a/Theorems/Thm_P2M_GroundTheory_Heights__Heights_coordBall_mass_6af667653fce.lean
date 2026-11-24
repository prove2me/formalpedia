-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
-- name    : P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:54.711883+00:00
-- url     : https://prove2.me/theorems/7bbe9e28-3ca3-4f7a-823e-e48c93e980de
-- title:
--   P2 M Ground Theory Heights  Heights coord Ball mass 6af667653fce: P2 M Ground Theory Heights  Heights coord Ball mass 6af667653fce
-- statement:
--   The P2 M Ground Theory Heights  Heights coord Ball mass 6af667653fce construction uses the P2 M Ground Theory Heights  Heights coord Ball mass 6af667653fce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralMass.lean#L29-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralMass.lean#L29-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
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
open MvPolynomial MeasureTheory Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coordBall_mass» := P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
