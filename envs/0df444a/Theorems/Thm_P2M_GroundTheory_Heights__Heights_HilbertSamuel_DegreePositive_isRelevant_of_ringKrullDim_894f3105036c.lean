-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_isRelevant_of_ringKrullDim_894f3105036c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_isRelevant_of_ringKrullDim_894f3105036c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:53.51052+00:00
-- url     : https://prove2.me/theorems/87e37f17-5c4d-4426-9761-f2309fbe9505
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive is Relevant of ring Krull Dim 894f3105036c: P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive is Relevant of ring Kr
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive is Relevant of ring Krull Dim 894f3105036c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive is Relevant of ring Krull Dim 894f3105036c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L72-L98

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
omit [Fintype ι₀]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_isRelevant_of_ringKrullDim_894f3105036c (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«DegreePositive».«isRelevant_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_isRelevant_of_ringKrullDim_894f3105036c
