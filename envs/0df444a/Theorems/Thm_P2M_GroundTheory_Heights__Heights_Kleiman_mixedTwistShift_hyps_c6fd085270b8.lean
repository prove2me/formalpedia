-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mixedTwistShift_hyps_c6fd085270b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mixedTwistShift_hyps_c6fd085270b8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:57.117608+00:00
-- url     : https://prove2.me/theorems/915a2622-acae-5a98-b752-ff867768853f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mixed Twist Shift hyps c6fd085270b8: P2 M Ground Theory Heights  Heights Kleiman mixed Twist Shift hyps c6fd085270b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mixed Twist Shift hyps c6fd085270b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman mixed Twist Shift hyps c6fd085270b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StMixedTwistShift.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StMixedTwistShift.lean#L25-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mixedTwistShift_hyps_c6fd085270b8 (k : Type u) [Field k] :
    (primeOf (S := k) (genericPt k 1)).IsPrime ∧
      (∀ f ∈ primeOf (S := k) (genericPt k 1), ∀ d : ℕ,
        homogeneousComponent d f ∈ primeOf (S := k) (genericPt k 1)) ∧
      primeOf (S := k) (genericPt k 1) ≤ primeOf (S := k) (genericPt k 1) ∧
      ringKrullDim (Poly k 1 ⧸ primeOf (S := k) (genericPt k 1)) ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      Nonempty (Fin 1 → LineBundle k (genericPt k 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mixedTwistShift_hyps» := P2M_GroundTheory_Heights__Heights_Kleiman_mixedTwistShift_hyps_c6fd085270b8
