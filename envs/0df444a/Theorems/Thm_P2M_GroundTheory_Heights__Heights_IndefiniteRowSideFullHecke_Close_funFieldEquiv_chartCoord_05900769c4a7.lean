-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_chartCoord_05900769c4a7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_chartCoord_05900769c4a7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:24:33.302046+00:00
-- url     : https://prove2.me/theorems/8a20dd5d-20f0-5c9a-8e56-562b40e06b0c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv chart Coord 05900769c4a7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv chart Coord 05900769c4a7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv chart Coord 05900769c4a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_chartCoord_05900769c4a7 (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funFieldEquiv P (P.chartCoord c v) = genPt P v / genPt P ⟨v.1, c v.1⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«funFieldEquiv_chartCoord» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_chartCoord_05900769c4a7
