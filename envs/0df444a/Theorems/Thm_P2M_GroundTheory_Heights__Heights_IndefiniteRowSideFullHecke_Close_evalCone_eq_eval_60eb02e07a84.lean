-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:37.676811+00:00
-- url     : https://prove2.me/theorems/00be8dbc-c858-570e-badc-648e6eb09c7a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close eval Cone eq eval 60eb02e07a84: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close eval Cone eq eval 60eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close eval Cone eq eval 60eb02e07a84 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close eval Cone eq eval 60eb02e07a84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L178-L184

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84 (z : Cone (oneBlockSizes e r) ℂ) (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    evalCone z f = eval (coneToPairs z) (map (Int.castRingHom ℂ) (rename (oneBlockReindex e r) f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«evalCone_eq_eval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84
