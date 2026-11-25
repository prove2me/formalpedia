-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:28.837223+00:00
-- url     : https://prove2.me/theorems/e4f325dc-3748-4998-b675-1033e1cbcfad
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out sum c0d7e90ce723: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out sum c0d7e90ce723
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out sum c0d7e90ce723 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff push Out sum c0d7e90ce723 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L289-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L289-L299

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723 (r a : ℕ) (c : SmallBlock) (κ : ℚ) (s : Finset (Fin r → ℕ))
    (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    constantCoeff (∑ lam ∈ s, b lam • pushOut r a c κ lam) =
      if rectangle r a ∈ s then b (rectangle r a) * κ else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_pushOut_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723
