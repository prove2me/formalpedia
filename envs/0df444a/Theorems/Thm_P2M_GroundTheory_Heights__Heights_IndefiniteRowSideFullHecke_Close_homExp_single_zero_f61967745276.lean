-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_zero_f61967745276
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_zero_f61967745276
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:48.092684+00:00
-- url     : https://prove2.me/theorems/078f83c4-1c4c-4fad-92b9-103dfb877248
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Exp single zero f61967745276: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Exp single zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Exp single zero f61967745276 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Exp single zero f61967745276 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L32-L36

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_zero_f61967745276 : homExp r (Finsupp.single 0 1) = Finsupp.single (Sum.inl ()) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«homExp_single_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_zero_f61967745276
