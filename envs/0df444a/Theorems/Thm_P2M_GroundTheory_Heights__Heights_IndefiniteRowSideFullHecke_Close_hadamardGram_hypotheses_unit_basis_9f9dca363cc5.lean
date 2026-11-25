-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hadamardGram_hypotheses_unit_basis_9f9dca363cc5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hadamardGram_hypotheses_unit_basis_9f9dca363cc5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:25.816483+00:00
-- url     : https://prove2.me/theorems/1263892b-1573-452d-85d4-adfe8d1a298d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hadamard Gram hypotheses unit basis 9f9dca363cc5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hada
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hadamard Gram hypotheses unit basis 9f9dca363cc5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hadamard Gram hypotheses unit basis 9f9dca363cc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L692-L699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L692-L699

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
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
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hadamardGram_hypotheses_unit_basis_9f9dca363cc5 :
    LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ i, ‖EuclideanSpace.basisFun (Fin 1) ℝ i‖ ≤ 1) ∧
      ∀ i, EuclideanSpace.basisFun (Fin 1) ℝ i ∈
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«hadamardGram_hypotheses_unit_basis» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hadamardGram_hypotheses_unit_basis_9f9dca363cc5
