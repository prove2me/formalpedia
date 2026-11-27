-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneToPairs_oneBlockPoint_e2eed756f9a6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneToPairs_oneBlockPoint_e2eed756f9a6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:22.329956+00:00
-- url     : https://prove2.me/theorems/4f9a8855-9264-5ab8-8be9-7a5b83a52d19
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone To Pairs one Block Point e2eed756f9a6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone To Pa
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone To Pairs one Block Point e2eed756f9a6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone To Pairs one Block Point e2eed756f9a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L208-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L208-L212

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
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneToPairs_oneBlockPoint_e2eed756f9a6 {F : Type*} [CommRing F] (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (σ : K →+* F) (w : Fin (r + 1) → F) :
    coneToPairs (oneBlockPoint om σ w) = fun p ↦ σ (om p.2.1 : K) * w p.2.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«coneToPairs_oneBlockPoint» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneToPairs_oneBlockPoint_e2eed756f9a6
