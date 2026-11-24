-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:35.856391+00:00
-- url     : https://prove2.me/theorems/29568552-2799-49f3-90ea-d289c02dd7ef
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle ext Map new Coord 1cebe4ed4869: P2 M Ground Theory Heights  Heights Section Cycle ext Map new Coord 1cebe4ed4869
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle ext Map new Coord 1cebe4ed4869 construction uses the P2 M Ground Theory Heights  Heights Section Cycle ext Map new Coord 1cebe4ed4869 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L165-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869 (j : Fin (D.size + 1)) :
    D.extMap (X (D.newCoord j)) = C (D.elt j) * X none := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«extMap_newCoord» := P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869
