-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_pos_40860eca4d99
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_pos_40860eca4d99
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:06.729186+00:00
-- url     : https://prove2.me/theorems/3564fc76-fd29-45ab-8e36-8d7e14fdb4b3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive pos 40860eca4d99: P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive pos 40860eca4d99
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive pos 40860eca4d99 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive pos 40860eca4d99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L147-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L147-L230

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_pos_40860eca4d99 (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«DegreePositive».«pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_pos_40860eca4d99
