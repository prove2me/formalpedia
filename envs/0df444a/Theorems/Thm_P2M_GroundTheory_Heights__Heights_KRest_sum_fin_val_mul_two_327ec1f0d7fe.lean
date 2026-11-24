-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe
-- name    : P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:13.937816+00:00
-- url     : https://prove2.me/theorems/075c0126-3e4f-426b-ae4a-2418525c3155
-- title:
--   P2 M Ground Theory Heights  Heights KRest sum fin val mul two 327ec1f0d7fe: P2 M Ground Theory Heights  Heights KRest sum fin val mul two 327ec1f0d7fe
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest sum fin val mul two 327ec1f0d7fe construction uses the P2 M Ground Theory Heights  Heights KRest sum fin val mul two 327ec1f0d7fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L68-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«sum_fin_val_mul_two» := P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe
