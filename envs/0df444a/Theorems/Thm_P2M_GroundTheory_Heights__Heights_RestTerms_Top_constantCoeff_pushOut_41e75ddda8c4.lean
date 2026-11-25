-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:31.307769+00:00
-- url     : https://prove2.me/theorems/018dd6b3-41d3-447d-a446-597ff685d0d0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out 41e75ddda8c4: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out 41e75ddda8c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out 41e75ddda8c4 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out 41e75ddda8c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L236-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L236-L254

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4 (r a : ℕ) (c : SmallBlock) (κ : ℚ) (lam : Fin r → ℕ)
    (hl : Antitone lam) :
    constantCoeff (pushOut r a c κ lam) = if lam = rectangle r a then κ else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_pushOut» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4
