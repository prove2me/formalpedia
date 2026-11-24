-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:17.027155+00:00
-- url     : https://prove2.me/theorems/d9764b9f-ed76-4be1-9971-14964f5c52fd
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one eq sum 351aebacb5b4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one eq sum 351a
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one eq sum 351aebacb5b4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one eq sum 351aebacb5b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L27-L31

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4 (d : Coord n →₀ ℕ) :
    Finsupp.weight 1 d = ∑ k, Finsupp.weight (coordDeg n) d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«weight_one_eq_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4
