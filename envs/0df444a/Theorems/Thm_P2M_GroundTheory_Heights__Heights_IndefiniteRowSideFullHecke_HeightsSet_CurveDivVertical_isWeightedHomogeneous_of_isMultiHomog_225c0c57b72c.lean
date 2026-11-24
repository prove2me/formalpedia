-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:23.980043+00:00
-- url     : https://prove2.me/theorems/b0c8358e-691f-4349-836d-fec1bbb65a42
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical is Weighted Homogeneous of is Multi Homog 225c0c57b72c: P2 M Ground Theory Heights  Heights Indefinite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical is Weighted Homogeneous of is Multi Homog 225c0c57b72c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical is Weighted Homogeneous of is Multi Homog 225c0c57b72c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L102-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L102-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c (T : Finset K) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (wt T) f (∑ k, if k ∈ T then a k else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CurveDivVertical».«isWeightedHomogeneous_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
