-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:31.516456+00:00
-- url     : https://prove2.me/theorems/413b0daf-94d7-4374-910d-2d924eabbe11
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of X ne zero c074763c9980: P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of X ne zero c074763c9980
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of X ne zero c074763c9980 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of X ne zero c074763c9980 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L28-L35

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980 (f N : ℕ) (τ : Fin f) :
    vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«vandermondeOf_X_ne_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980
