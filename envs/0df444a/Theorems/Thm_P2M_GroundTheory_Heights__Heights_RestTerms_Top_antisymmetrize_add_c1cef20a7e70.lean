-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:56.835062+00:00
-- url     : https://prove2.me/theorems/0285d73a-d5c2-4c5e-9376-2009a5508b7d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize add c1cef20a7e70: P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize add c1cef20a7e70
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize add c1cef20a7e70 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize add c1cef20a7e70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70 (f N : ℕ) (H H' : RootRing f N) :
    antisymmetrize f N (H + H') = antisymmetrize f N H + antisymmetrize f N H' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antisymmetrize_add» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70
