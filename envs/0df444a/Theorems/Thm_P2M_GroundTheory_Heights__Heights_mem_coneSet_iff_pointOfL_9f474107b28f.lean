-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f
-- name    : P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:53.811783+00:00
-- url     : https://prove2.me/theorems/3a3dd34e-356f-4859-ac5f-097f72fbb82c
-- title:
--   P2 M Ground Theory Heights  Heights mem cone Set iff point Of L 9f474107b28f: P2 M Ground Theory Heights  Heights mem cone Set iff point Of L 9f474107b28f
-- statement:
--   The P2 M Ground Theory Heights  Heights mem cone Set iff point Of L 9f474107b28f construction uses the P2 M Ground Theory Heights  Heights mem cone Set iff point Of L 9f474107b28f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L34-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : y ∈ coneSet h J ↔ h.pointOfL y ∈ zeroSetEuc J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_coneSet_iff_pointOfL» := P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f
