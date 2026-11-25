-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_hasStrictFDerivAt_equiv_cba9f8ca6ee6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_hasStrictFDerivAt_equiv_cba9f8ca6ee6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:44.388934+00:00
-- url     : https://prove2.me/theorems/869dc999-e390-5ca9-a90b-5554e52fb17a
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds has Strict FDeriv At equiv cba9f8ca6ee6: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds has Strict FDeriv At
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds has Strict FDeriv At equiv cba9f8ca6ee6 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds has Strict FDeriv At equiv cba9f8ca6ee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L50-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_hasStrictFDerivAt_equiv_cba9f8ca6ee6 {n : ℕ} {Q : (Fin n → ℂ) → (Fin n → ℂ)} {u : Fin n → ℂ}
    (hQ : AnalyticAt ℂ Q u)
    (hd : LinearMap.det (fderiv ℂ Q u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), HasStrictFDerivAt Q (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«hasStrictFDerivAt_equiv» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_hasStrictFDerivAt_equiv_cba9f8ca6ee6
