-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:10:56.924441+00:00
-- url     : https://prove2.me/theorems/03f36513-11c9-53ed-a6f4-c4b92193caa6
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim minimal Prime fb3bba25115f: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim minimal Prime fb3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim minimal Prime fb3bba25115f construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim minimal Prime fb3bba25115f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L219-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L219-L243

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f [Fintype K] [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι F)}
    [P.IsPrime] {s : MRing ι F} (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes)
    {e : ℕ} (hdim : ringKrullDim (MRing ι F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«ringKrullDim_minimalPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f
