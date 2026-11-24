-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:14.497746+00:00
-- url     : https://prove2.me/theorems/cd7569cb-0610-4b4b-aaa7-807077b3d5e6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map monomial be73811eb40e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map monomial be7381
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map monomial be73811eb40e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map monomial be73811eb40e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L52-L55

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
variable (K : Type) [Field K] (r : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e (s : Fin (r + 1) →₀ ℕ) (c : K) :
    homMap K r (monomial s c) = monomial (homExp r s) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«homMap_monomial» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e
