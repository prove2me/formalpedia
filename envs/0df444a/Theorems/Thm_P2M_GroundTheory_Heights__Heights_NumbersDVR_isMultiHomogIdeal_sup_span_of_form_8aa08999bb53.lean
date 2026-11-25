-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:11.091064+00:00
-- url     : https://prove2.me/theorems/2d4310c5-70fd-4b90-b6b2-53a7c1f60893
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span of form 8aa08999bb53: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span of form 8aa08999bb53
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span of form 8aa08999bb53 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span of form 8aa08999bb53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
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
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53 {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_sup_span_of_form» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53
