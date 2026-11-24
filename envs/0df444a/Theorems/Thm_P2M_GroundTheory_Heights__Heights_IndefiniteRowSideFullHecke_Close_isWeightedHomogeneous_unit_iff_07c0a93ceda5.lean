-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:07.731412+00:00
-- url     : https://prove2.me/theorems/37f89906-e14a-4ef0-b8e8-1622e9ecab72
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Weighted Homogeneous unit iff 07c0a93ceda5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Weig
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Weighted Homogeneous unit iff 07c0a93ceda5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close is Weighted Homogeneous unit iff 07c0a93ceda5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L94-L105

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5 {r m : ℕ} (f : MvPolynomial (Coord (fun _ : Unit ↦ r)) ℤ) :
    IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ r)) f (fun _ ↦ m) ↔ f.IsHomogeneous m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«isWeightedHomogeneous_unit_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5
