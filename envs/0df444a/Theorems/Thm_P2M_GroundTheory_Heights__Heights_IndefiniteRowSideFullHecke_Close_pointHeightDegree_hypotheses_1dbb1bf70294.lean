-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_1dbb1bf70294
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_1dbb1bf70294
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:10.299254+00:00
-- url     : https://prove2.me/theorems/ff96089e-3e0c-5384-b36e-d0bd8b4c80b5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses 1dbb1bf70294: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Hei
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses 1dbb1bf70294 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close point Height Degree hypotheses 1dbb1bf70294 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L231-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L231-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
open Matrix
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_1dbb1bf70294 (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (F : HermLattice K (r + 1)) (A : HermLine (oneBlockSizes e r)) (hA : A.deg = 1)
    (hM : OneBlockMetricAgrees om F A) :
    (∀ σ, (F.metric σ).PosDef) ∧
      (∀ σ, F.metric (ComplexEmbedding.conjugate σ) = (F.metric σ).map (starRingEnd ℂ)) ∧
      (∀ u, A.deg u = 1) ∧
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«pointHeightDegree_hypotheses» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pointHeightDegree_hypotheses_1dbb1bf70294
