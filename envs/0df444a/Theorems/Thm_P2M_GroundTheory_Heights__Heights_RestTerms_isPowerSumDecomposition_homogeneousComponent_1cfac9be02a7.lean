-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_isPowerSumDecomposition_homogeneousComponent_1cfac9be02a7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_isPowerSumDecomposition_homogeneousComponent_1cfac9be02a7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:26.433741+00:00
-- url     : https://prove2.me/theorems/e89dca74-d28f-4d5d-a758-ba0e149c8e35
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms is Power Sum Decomposition homogeneous Component 1cfac9be02a7: P2 M Ground Theory Heights  Heights Rest Terms is Power Sum Decomposition homogeneous Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms is Power Sum Decomposition homogeneous Component 1cfac9be02a7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms is Power Sum Decomposition homogeneous Component 1cfac9be02a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L166-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L166-L194

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_isPowerSumDecomposition_homogeneousComponent_1cfac9be02a7 (f N : ℕ) (F : RootRing f N)
    (Q : ℕ → Fin f → RootRing f N) (hF : F.IsHomogeneous (topDegree f N + 1))
    (hQ : IsPowerSumDecomposition f N F Q) :
    IsPowerSumDecomposition f N F
        (fun m τ => homogeneousComponent (topDegree f N + 1 - m) (Q m τ)) ∧
      ∀ m τ, (homogeneousComponent (topDegree f N + 1 - m) (Q m τ)).IsHomogeneous
        (topDegree f N + 1 - m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«isPowerSumDecomposition_homogeneousComponent» := P2M_GroundTheory_Heights__Heights_RestTerms_isPowerSumDecomposition_homogeneousComponent_1cfac9be02a7
