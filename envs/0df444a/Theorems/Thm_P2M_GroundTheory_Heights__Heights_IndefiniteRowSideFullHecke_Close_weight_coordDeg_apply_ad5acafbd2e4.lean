-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:53.174735+00:00
-- url     : https://prove2.me/theorems/b0e8f6a3-01bb-447d-928a-59b850e7e0e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight coord Deg apply ad5acafbd2e4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight coord Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight coord Deg apply ad5acafbd2e4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight coord Deg apply ad5acafbd2e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L16-L25

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4 (d : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) d k = ∑ i, d ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«weight_coordDeg_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4
