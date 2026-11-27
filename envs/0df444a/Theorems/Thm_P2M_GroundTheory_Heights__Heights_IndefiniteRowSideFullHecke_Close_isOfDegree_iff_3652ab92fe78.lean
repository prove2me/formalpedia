-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isOfDegree_iff_3652ab92fe78
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isOfDegree_iff_3652ab92fe78
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:56.217508+00:00
-- url     : https://prove2.me/theorems/8e84920a-a68b-4ae1-b567-c0aff2a05fe0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Of Degree iff 3652ab92fe78: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Of Degree iff 3652ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Of Degree iff 3652ab92fe78 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Of Degree iff 3652ab92fe78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L82-L90

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isOfDegree_iff_3652ab92fe78 (P : ArithVariety n) (a : ι → ℤ) (x : P.FunField) :
    P.IsOfDegree a x ↔ IsHomogOfDeg P a (funFieldEquiv P x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«isOfDegree_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isOfDegree_iff_3652ab92fe78
