-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:30.156948+00:00
-- url     : https://prove2.me/theorems/bf3ac0a0-311f-4f20-a04e-1eab4842a4b5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR span forms of is Multi Homog Ideal 934319068e0f: P2 M Ground Theory Heights  Heights Numbers DVR span forms of is Multi Homog Ideal 934319068e0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR span forms of is Multi Homog Ideal 934319068e0f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR span forms of is Multi Homog Ideal 934319068e0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealMultiHomog.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealMultiHomog.lean#L22-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f {K : Type} [DecidableEq K] {ι : K → Type}
    {R : Type*} [CommRing R] {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) :
    Ideal.span {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b} = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«span_forms_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f
