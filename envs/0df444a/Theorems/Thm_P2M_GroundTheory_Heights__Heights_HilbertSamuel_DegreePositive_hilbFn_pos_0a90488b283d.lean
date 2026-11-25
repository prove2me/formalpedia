-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_hilbFn_pos_0a90488b283d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_hilbFn_pos_0a90488b283d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:02:29.407798+00:00
-- url     : https://prove2.me/theorems/fe402474-d6e8-53f0-ae44-4f0636458feb
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive hilb Fn pos 0a90488b283d: P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive hilb Fn pos 0a90488b283d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive hilb Fn pos 0a90488b283d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive hilb Fn pos 0a90488b283d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L102-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L102-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_hilbFn_pos_0a90488b283d (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«DegreePositive».«hilbFn_pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_hilbFn_pos_0a90488b283d
