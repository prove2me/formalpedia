-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:17.052803+00:00
-- url     : https://prove2.me/theorems/4f6e8da1-118b-44ea-9d4f-756bbd28644b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion is Multi Homog of lex e97f02c5fe46: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion is Multi Hom
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion is Multi Homog of lex e97f02c5fe46 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion is Multi Homog of lex e97f02c5fe46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
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
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46 {x : MRing ι R} {i : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : IsWeightedHomogeneous (lexDeg ∘ blockWeight ι) x i) : ∃ s, IsMultiHomog x s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«isMultiHomog_of_lex» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46
