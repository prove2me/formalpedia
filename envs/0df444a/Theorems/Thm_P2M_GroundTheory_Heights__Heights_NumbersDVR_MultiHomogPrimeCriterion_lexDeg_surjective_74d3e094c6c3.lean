-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:03.696324+00:00
-- url     : https://prove2.me/theorems/c583bc98-f9e9-4c88-ab3c-9879393410ad
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg surjective 74d3e094c6c3: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg surject
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg surjective 74d3e094c6c3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion lex Deg surjective 74d3e094c6c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L32-L39

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3 : Function.Surjective (lexDeg (K := K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«lexDeg_surjective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
