-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_b9be1e38941d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_b9be1e38941d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:34.436971+00:00
-- url     : https://prove2.me/theorems/9a9ddda6-f43c-451d-8dff-9e8fd5db7a63
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span b9be1e38941d: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span b9be1e38941d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span b9be1e38941d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal sup span b9be1e38941d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L32-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_b9be1e38941d {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} {J : Ideal (MRing ι R)} {f : MRing ι R} {s : K → ℕ}
    (hJ : IsMultiHomogIdeal J) (hf : IsMultiHomog f s) :
    IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_b9be1e38941d
