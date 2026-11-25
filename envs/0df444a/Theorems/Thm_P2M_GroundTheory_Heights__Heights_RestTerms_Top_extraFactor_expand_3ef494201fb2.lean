-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:33.577298+00:00
-- url     : https://prove2.me/theorems/cb35adb9-cee4-4101-a8a3-6bcc7c2bfa04
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top extra Factor expand 3ef494201fb2: P2 M Ground Theory Heights  Heights Rest Terms Top extra Factor expand 3ef494201fb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top extra Factor expand 3ef494201fb2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top extra Factor expand 3ef494201fb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L333-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L333-L349

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2 (hF : FrobeniusCharacterFormula.Statement) (r q m : ℕ) :
    extraFactor r q * psum (Fin r) ℚ 1 ^ m =
      ∑ lam ∈ partitionsOf r (q + m), C (blockCoeff q m lam) * schur (Fin r) lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«extraFactor_expand» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2
