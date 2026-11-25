-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:41.705614+00:00
-- url     : https://prove2.me/theorems/d908b9fe-a29b-5cdf-93df-ed3020da4bd5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD of divided Difference eq 219f21cc1918: P2 M Ground Theory Heights  Heights Rest Terms Top has DD of divided Difference eq 219f21cc1918
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD of divided Difference eq 219f21cc1918 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD of divided Difference eq 219f21cc1918 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L46-L52

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918 {f N : ℕ} {H P : RootRing f N}
    (h : dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P) :
    HasDD f N H P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_of_dividedDifference_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918
