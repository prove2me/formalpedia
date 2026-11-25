-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_mkF_X_adb6f18f8715
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_mkF_X_adb6f18f8715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:22.209019+00:00
-- url     : https://prove2.me/theorems/b300edd9-ebb6-4a0e-ac8e-e133b91d1839
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv mk F X adb6f18f8715: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv m
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv mk F X adb6f18f8715 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv mk F X adb6f18f8715 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_mkF_X_adb6f18f8715 (P : ArithVariety n) (v : Coord n) :
    funFieldEquiv P (P.mkF (X v)) = genPt P v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«funFieldEquiv_mkF_X» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_mkF_X_adb6f18f8715
