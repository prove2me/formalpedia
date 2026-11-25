-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:35.116799+00:00
-- url     : https://prove2.me/theorems/56f702bc-a159-5541-b478-aad79bfc3e33
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms hsymm is Homogeneous fa4efb84373b: P2 M Ground Theory Heights  Heights Rest Terms hsymm is Homogeneous fa4efb84373b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms hsymm is Homogeneous fa4efb84373b construction uses the P2 M Ground Theory Heights  Heights Rest Terms hsymm is Homogeneous fa4efb84373b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurHomogeneous.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSchurHomogeneous.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«hsymm_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b
