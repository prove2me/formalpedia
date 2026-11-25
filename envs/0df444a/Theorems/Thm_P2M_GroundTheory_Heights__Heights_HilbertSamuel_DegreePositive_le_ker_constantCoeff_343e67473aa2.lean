-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_le_ker_constantCoeff_343e67473aa2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_le_ker_constantCoeff_343e67473aa2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:38.088836+00:00
-- url     : https://prove2.me/theorems/5f4827ab-ef83-4b15-a347-605266f91dca
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive le ker constant Coeff 343e67473aa2: P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive le ker constant Coeff 343e6747
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive le ker constant Coeff 343e67473aa2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive le ker constant Coeff 343e67473aa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L132-L145

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_le_ker_constantCoeff_343e67473aa2 (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«DegreePositive».«le_ker_constantCoeff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_le_ker_constantCoeff_343e67473aa2
