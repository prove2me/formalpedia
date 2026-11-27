-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_sum_833b8cb4f103
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_sum_833b8cb4f103
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:32.17789+00:00
-- url     : https://prove2.me/theorems/4c304cca-f462-5b6f-bbd8-14811503b8bf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize sum 833b8cb4f103: P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize sum 833b8cb4f103
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize sum 833b8cb4f103 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize sum 833b8cb4f103 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L62-L67

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_sum_833b8cb4f103 {ι : Type*} (s : Finset ι) (f N : ℕ) (H : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, H i) = ∑ i ∈ s, antisymmetrize f N (H i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antisymmetrize_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_sum_833b8cb4f103
