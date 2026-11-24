-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_first_18648e576495
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_first_18648e576495
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:34.463064+00:00
-- url     : https://prove2.me/theorems/da87cdcd-8507-47a8-8ffc-49b8f2665533
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu first 18648e576495: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu first 18648e576495
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu first 18648e576495 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu first 18648e576495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L101-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_first_18648e576495 (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (smallBlockMu f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f r a false := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_smallBlockMu_first» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_first_18648e576495
