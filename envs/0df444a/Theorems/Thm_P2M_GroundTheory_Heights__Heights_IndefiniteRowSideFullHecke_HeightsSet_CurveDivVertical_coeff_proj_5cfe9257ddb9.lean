-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_coeff_proj_5cfe9257ddb9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_coeff_proj_5cfe9257ddb9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:56.232214+00:00
-- url     : https://prove2.me/theorems/3c587a3f-7acb-4a6b-a335-5a0a78788578
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical coeff proj 5cfe9257ddb9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical coeff proj 5cfe9257ddb9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical coeff proj 5cfe9257ddb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_coeff_proj_5cfe9257ddb9 (T : Finset K) (f : MRing ι) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (proj T f) = if ∀ p, d p ≠ 0 → p.1 ∉ T then coeff d f else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CurveDivVertical».«coeff_proj» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_coeff_proj_5cfe9257ddb9
