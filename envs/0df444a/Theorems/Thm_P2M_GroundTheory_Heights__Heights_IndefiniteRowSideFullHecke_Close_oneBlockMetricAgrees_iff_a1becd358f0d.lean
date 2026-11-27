-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockMetricAgrees_iff_a1becd358f0d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockMetricAgrees_iff_a1becd358f0d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:07.516933+00:00
-- url     : https://prove2.me/theorems/14ade0d0-4813-590f-b592-500519cca11d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Metric Agrees iff a1becd358f0d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Me
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Metric Agrees iff a1becd358f0d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Metric Agrees iff a1becd358f0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L223-L229

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockMetricAgrees_iff_a1becd358f0d (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (F : HermLattice K (r + 1))
    (A : HermLine (oneBlockSizes e r)) :
    OneBlockMetricAgrees om F A ↔
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«oneBlockMetricAgrees_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockMetricAgrees_iff_a1becd358f0d
