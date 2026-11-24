-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_last_5f162ecc6d85
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_last_5f162ecc6d85
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:27.699582+00:00
-- url     : https://prove2.me/theorems/e502a42b-9991-43ba-946b-427a7e33717f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu last 5f162ecc6d85: P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu last 5f162ecc6d85
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu last 5f162ecc6d85 construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Ring To Real small Block Mu last 5f162ecc6d85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L93-L99

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_last_5f162ecc6d85 (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallBlockMu f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f a r true := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootRingToReal_smallBlockMu_last» := P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_last_5f162ecc6d85
