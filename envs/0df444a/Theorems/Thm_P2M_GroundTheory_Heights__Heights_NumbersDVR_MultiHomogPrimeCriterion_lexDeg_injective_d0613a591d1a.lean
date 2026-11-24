-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:59.84881+00:00
-- url     : https://prove2.me/theorems/742244c8-83a5-431f-ba69-792b5f09eca8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg injective d0613a591d1a: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg injectiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg injective d0613a591d1a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg injective d0613a591d1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L23-L29

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a : Function.Injective (lexDeg (K := K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«lexDeg_injective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a
