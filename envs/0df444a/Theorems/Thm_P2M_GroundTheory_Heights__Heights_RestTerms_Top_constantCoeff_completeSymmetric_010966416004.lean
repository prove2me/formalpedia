-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:21.506257+00:00
-- url     : https://prove2.me/theorems/ef407d72-b73f-435e-9102-71d9df334785
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff complete Symmetric 010966416004: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff complete Symmetric 010966416004
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff complete Symmetric 010966416004 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff complete Symmetric 010966416004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L179-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L179-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004 (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) :
    constantCoeff (completeSymmetric σ d) = if d = 0 then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_completeSymmetric» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004
