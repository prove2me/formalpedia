-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:44.635329+00:00
-- url     : https://prove2.me/theorems/86f2bbad-61a0-48a5-8c76-4a903a7da6b0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms small Block Place eq 24505b87eaf7: P2 M Ground Theory Heights  Heights Rest Terms small Block Place eq 24505b87eaf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms small Block Place eq 24505b87eaf7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms small Block Place eq 24505b87eaf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAntisymmetrizePlace.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAntisymmetrizePlace.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAntisymmetrizePlace
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7 (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«smallBlockPlace_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7
