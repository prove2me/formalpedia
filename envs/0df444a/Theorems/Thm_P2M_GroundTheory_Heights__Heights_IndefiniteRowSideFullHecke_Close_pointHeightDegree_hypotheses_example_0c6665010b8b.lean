-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_example_0c6665010b8b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_example_0c6665010b8b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:41.210921+00:00
-- url     : https://prove2.me/theorems/417ff13f-a854-5708-96f1-e82d06b5c093
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses example 0c6665010b8b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close p
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses example 0c6665010b8b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses example 0c6665010b8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L747-L781
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L747-L781

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
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_example_0c6665010b8b :
    (∀ σ : ℚ →+* ℂ, ((fun _ : ℚ →+* ℂ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) σ).PosDef) ∧
    (∀ σ : ℚ →+* ℂ, (fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (ComplexEmbedding.conjugate σ) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ).map (starRingEnd ℂ)) ∧
    (∀ u, (HermLine.standard (fun _ : Unit ↦ 0)).deg u = 1) ∧
    (∀ (σ : ℚ →+* ℂ) (w : Fin 1 → ℂ), w ≠ 0 →
      (HermLine.standard (fun _ : Unit ↦ 0)).metric
          (fun _ t ↦ σ (ratBasis (pairEquiv.symm t).1 : ℚ) *
            w (pairEquiv.symm t).2) =
        hermNorm 1 w) ∧
    (∀ (σ' : ℚ →+* ℂ) (x y : (HermitianBundle.standard ℚ 1).carrier),
      ((HermitianBundle.standard ℚ 1).metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] x)
          ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] y) =
        star (fun j ↦ σ' (stdPhi x j : ℚ)) ⬝ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun j ↦ σ' (stdPhi y j : ℚ))) ∧
    (fun _ ↦ (1 : 𝓞 ℚ) : Fin 1 → 𝓞 ℚ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«pointHeightDegree_hypotheses_example» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_example_0c6665010b8b
