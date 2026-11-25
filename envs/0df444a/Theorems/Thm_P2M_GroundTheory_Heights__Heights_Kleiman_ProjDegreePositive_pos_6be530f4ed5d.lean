-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_pos_6be530f4ed5d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_pos_6be530f4ed5d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:24.495969+00:00
-- url     : https://prove2.me/theorems/56adb67a-88e8-4710-b5c4-3d63b3a00178
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive pos 6be530f4ed5d: P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive pos 6be530f4ed5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive pos 6be530f4ed5d construction uses the P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive pos 6be530f4ed5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L149-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L149-L232

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_pos_6be530f4ed5d (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ProjDegreePositive».«pos» := P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_pos_6be530f4ed5d
