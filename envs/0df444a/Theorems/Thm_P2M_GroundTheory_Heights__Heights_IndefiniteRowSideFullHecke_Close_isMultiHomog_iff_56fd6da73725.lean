-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:39.539452+00:00
-- url     : https://prove2.me/theorems/98235e49-d69f-5e81-aa36-22a509a295ac
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Multi Homog iff 56fd6da73725: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Multi Homog iff 56
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Multi Homog iff 56fd6da73725 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Multi Homog iff 56fd6da73725 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L44-L52

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725 (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    IsMultiHomog (ι := fun k ↦ Fin (n k + 1)) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725
