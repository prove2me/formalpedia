-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_ringKrullDim_of_mem_minimalPrimes_c3b0ffc6dd58
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_ringKrullDim_of_mem_minimalPrimes_c3b0ffc6dd58
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:58:14.233712+00:00
-- url     : https://prove2.me/theorems/af518497-8212-4d17-9f86-33a238843c54
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive ring Krull Dim of mem minimal Primes c3b0ffc6dd58: P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive ring Krull Dim of m
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive ring Krull Dim of mem minimal Primes c3b0ffc6dd58 construction uses the P2 M Ground Theory Heights  Heights Kleiman Proj Degree Positive ring Krull Dim of mem minimal Primes c3b0ffc6dd58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L21-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean#L21-L70

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_ringKrullDim_of_mem_minimalPrimes_c3b0ffc6dd58 (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ProjDegreePositive».«ringKrullDim_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Kleiman_ProjDegreePositive_ringKrullDim_of_mem_minimalPrimes_c3b0ffc6dd58
