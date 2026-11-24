-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:14.349805+00:00
-- url     : https://prove2.me/theorems/fd67470b-735c-44d0-b6ff-88be69908454
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value eval  monomial cone 2bc04389d40a: P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value eval  monomial cone 2bc043
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value eval  monomial cone 2bc04389d40a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value eval  monomial cone 2bc04389d40a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PProjIdealFormValue.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PProjIdealFormValue.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a {F Φ : Type*} [CommRing F] [CommRing Φ] (α : F →+* Φ) {K : Type*}
    {ι : K → Type*} (z : (Σ k, ι k) → Φ) (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    eval₂ (C.comp α) (fun p => C (z p) * X p.1) (monomial m c) =
      C (eval₂ α z (monomial m c)) * monomial (Finsupp.mapDomain Sigma.fst m) (1 : Φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ProjIdealFormValue».«eval₂_monomial_cone» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a
