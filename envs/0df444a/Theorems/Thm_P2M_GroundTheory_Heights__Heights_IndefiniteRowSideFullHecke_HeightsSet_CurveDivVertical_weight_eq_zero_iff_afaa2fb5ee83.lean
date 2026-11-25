-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_weight_eq_zero_iff_afaa2fb5ee83
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_weight_eq_zero_iff_afaa2fb5ee83
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:04.533102+00:00
-- url     : https://prove2.me/theorems/68cab8f0-8e7d-43d2-9a04-2d030e069e64
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical weight eq zero iff afaa2fb5ee83: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical weight eq zero iff afaa2fb5ee83 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Curve Div Vertical weight eq zero iff afaa2fb5ee83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCurveDivVertical.lean#L31-L38

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_weight_eq_zero_iff_afaa2fb5ee83 {σ : Type*} (w : σ → ℕ) (d : σ →₀ ℕ) :
    Finsupp.weight w d = 0 ↔ ∀ p, d p ≠ 0 → w p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«CurveDivVertical».«weight_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_weight_eq_zero_iff_afaa2fb5ee83
