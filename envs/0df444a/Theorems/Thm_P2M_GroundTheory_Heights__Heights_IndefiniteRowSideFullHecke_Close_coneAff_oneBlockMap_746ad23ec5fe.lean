-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:31.155976+00:00
-- url     : https://prove2.me/theorems/1da36876-0d87-403d-883d-7dc87d4dd431
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff one Block Map 746ad23ec5fe: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff one Bloc
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff one Block Map 746ad23ec5fe construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff one Block Map 746ad23ec5fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L129-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L129-L145

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    coneAff K r (oneBlockMap (r := r) om f) =
      mConeMap (oneBlockPt om r) (rename (oneBlockReindex e r) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«coneAff_oneBlockMap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe
