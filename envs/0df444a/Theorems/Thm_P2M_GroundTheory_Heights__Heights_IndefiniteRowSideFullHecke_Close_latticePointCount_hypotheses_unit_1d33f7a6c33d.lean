-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_latticePointCount_hypotheses_unit_1d33f7a6c33d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_latticePointCount_hypotheses_unit_1d33f7a6c33d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:16.825299+00:00
-- url     : https://prove2.me/theorems/44b95307-2149-5edf-b269-92d7fda88f27
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close lattice Point Count hypotheses unit 1d33f7a6c33d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close latt
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close lattice Point Count hypotheses unit 1d33f7a6c33d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close lattice Point Count hypotheses unit 1d33f7a6c33d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L701-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L701-L714

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_latticePointCount_hypotheses_unit_1d33f7a6c33d :
    (0 : ℝ) < 1 ∧ LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ s ∈ ({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))), ‖s‖ ≤ 1) ∧
      AddSubgroup.closure
          (({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))) :
            Set (EuclideanSpace ℝ (Fin 1))) =
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«latticePointCount_hypotheses_unit» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_latticePointCount_hypotheses_unit_1d33f7a6c33d
