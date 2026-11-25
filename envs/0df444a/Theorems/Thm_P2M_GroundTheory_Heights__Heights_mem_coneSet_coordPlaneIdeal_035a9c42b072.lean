-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
-- name    : P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:59.45886+00:00
-- url     : https://prove2.me/theorems/bbe5cddb-895a-42cd-8db2-0aad299aa35a
-- title:
--   P2 M Ground Theory Heights  Heights mem cone Set coord Plane Ideal 035a9c42b072: P2 M Ground Theory Heights  Heights mem cone Set coord Plane Ideal 035a9c42b072
-- statement:
--   The P2 M Ground Theory Heights  Heights mem cone Set coord Plane Ideal 035a9c42b072 construction uses the P2 M Ground Theory Heights  Heights mem cone Set coord Plane Ideal 035a9c42b072 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L62-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L62-L85

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

theorem P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072 {m k : ℕ} (y : EuclideanSpace ℂ (Fin (m + k))) :
    y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ↔
      ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_coneSet_coordPlaneIdeal» := P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
