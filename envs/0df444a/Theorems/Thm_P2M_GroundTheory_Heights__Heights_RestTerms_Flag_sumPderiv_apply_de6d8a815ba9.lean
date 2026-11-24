-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:22.094939+00:00
-- url     : https://prove2.me/theorems/f6d24aa9-819b-4cb9-b699-d00915c52a1f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv apply de6d8a815ba9: P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv apply de6d8a815ba9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv apply de6d8a815ba9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv apply de6d8a815ba9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L140-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L140-L147

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9 (s : Finset ι) (g : ι → σ) (P : MvPolynomial σ ℚ) :
    sumPderiv s g P = ∑ l ∈ s, pderiv (g l) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«sumPderiv_apply» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
