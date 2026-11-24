-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
-- name    : P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:55.401165+00:00
-- url     : https://prove2.me/theorems/32123d81-1318-44f6-b2d7-f8b70e3ccec1
-- title:
--   P2 M Ground Theory Heights  Heights ae coord Plane Block det ne zero 029df6309a2e: P2 M Ground Theory Heights  Heights ae coord Plane Block det ne zero 029df6309a2e
-- statement:
--   The P2 M Ground Theory Heights  Heights ae coord Plane Block det ne zero 029df6309a2e construction uses the P2 M Ground Theory Heights  Heights ae coord Plane Block det ne zero 029df6309a2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L176-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L176-L194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e (m k : ℕ) :
    ∀ᵐ π : Fin m → Fin (m + k) → ℂ, (coordPlaneBlock π).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ae_coordPlaneBlock_det_ne_zero» := P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
