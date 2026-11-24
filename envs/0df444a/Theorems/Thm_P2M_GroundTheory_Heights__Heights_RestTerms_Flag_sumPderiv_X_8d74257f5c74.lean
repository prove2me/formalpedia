-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:48.698421+00:00
-- url     : https://prove2.me/theorems/1e534c24-c4ff-4fff-a241-8ae6a60633e1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv X 8d74257f5c74: P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv X 8d74257f5c74
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv X 8d74257f5c74 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv X 8d74257f5c74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L149-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable {σ ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74 [DecidableEq σ] (s : Finset ι) (g : ι → σ) (v : σ) :
    sumPderiv s g (X v) = C (((s.filter fun l => g l = v).card : ℕ) : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«sumPderiv_X» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
