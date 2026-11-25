-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_ringKrullDim_of_mem_minimalPrimes_6ea4f2ae7cea
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_ringKrullDim_of_mem_minimalPrimes_6ea4f2ae7cea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:52.382801+00:00
-- url     : https://prove2.me/theorems/7569a758-718f-4cc1-83de-05fb0eaca047
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive ring Krull Dim of mem minimal Primes 6ea4f2ae7cea: P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive ring Krull Dim
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive ring Krull Dim of mem minimal Primes 6ea4f2ae7cea construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Degree Positive ring Krull Dim of mem minimal Primes 6ea4f2ae7cea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L19-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegreePositive.lean#L19-L68

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_ringKrullDim_of_mem_minimalPrimes_6ea4f2ae7cea (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«DegreePositive».«ringKrullDim_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_ringKrullDim_of_mem_minimalPrimes_6ea4f2ae7cea
