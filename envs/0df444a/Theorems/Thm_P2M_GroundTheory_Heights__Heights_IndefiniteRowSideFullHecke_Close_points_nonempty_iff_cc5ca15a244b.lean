-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:31.337564+00:00
-- url     : https://prove2.me/theorems/d026f8f1-ca06-4605-9221-89b0379d64e3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points nonempty iff cc5ca15a244b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points nonempty iff
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points nonempty iff cc5ca15a244b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points nonempty iff cc5ca15a244b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L254-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L254-L265

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
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
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b (hB : IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement) (P : ArithVariety n) (k₀ : ι) :
    (P.points ℂ).Nonempty ↔ (oneBlockPoints P k₀).Nonempty := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«points_nonempty_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b
