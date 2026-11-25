-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mCoordIdeal_eq_comap_081589c6f7ce
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mCoordIdeal_eq_comap_081589c6f7ce
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:15.619645+00:00
-- url     : https://prove2.me/theorems/d89dd7df-6102-5439-b4fa-03cc8c748a68
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close m Coord Ideal eq comap 081589c6f7ce: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close m Coord Ideal eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close m Coord Ideal eq comap 081589c6f7ce construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close m Coord Ideal eq comap 081589c6f7ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L162-L166

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mCoordIdeal_eq_comap_081589c6f7ce (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    mCoordIdeal (oneBlockPt om r) =
      (Heights.oneBlockIdeal (r := r) om).comap (rename (oneBlockReindexInv e r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mCoordIdeal_eq_comap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mCoordIdeal_eq_comap_081589c6f7ce
