-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042
-- name    : P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:24.795848+00:00
-- url     : https://prove2.me/theorems/3a38e149-901e-4a46-9e85-b8f5536644da
-- title:
--   P2 M Ground Theory Heights  Heights zero Ext apply of le 3705d4a23042: P2 M Ground Theory Heights  Heights zero Ext apply of le 3705d4a23042
-- statement:
--   The P2 M Ground Theory Heights  Heights zero Ext apply of le 3705d4a23042 construction uses the P2 M Ground Theory Heights  Heights zero Ext apply of le 3705d4a23042 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L95-L103

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

theorem P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042 {m k : ℕ} (x : EuclideanSpace ℂ (Fin m)) (j : Fin (m + k))
    (hj : m ≤ (j : ℕ)) : zeroExt m k x j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zeroExt_apply_of_le» := P2M_GroundTheory_Heights__Heights_zeroExt_apply_of_le_3705d4a23042
