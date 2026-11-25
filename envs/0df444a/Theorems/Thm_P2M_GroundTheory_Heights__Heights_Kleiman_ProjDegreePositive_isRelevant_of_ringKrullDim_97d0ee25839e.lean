-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_isRelevant_of_ringKrullDim_97d0ee25839e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_isRelevant_of_ringKrullDim_97d0ee25839e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:02:44.239682+00:00
-- url     : https://prove2.me/theorems/3bd5e385-5079-5110-a6b4-031b64046bf5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive is Relevant of ring Krull Dim 97d0ee25839e: P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive is Relevant of ring Krull
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive is Relevant of ring Krull Dim 97d0ee25839e construction uses the P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive is Relevant of ring Krull Dim 97d0ee25839e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L74-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L74-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PProjDegreePositive
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.ProjDegreePositive
variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]
omit [Fintype ι₀]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_isRelevant_of_ringKrullDim_97d0ee25839e (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ProjDegreePositive».«isRelevant_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_isRelevant_of_ringKrullDim_97d0ee25839e
