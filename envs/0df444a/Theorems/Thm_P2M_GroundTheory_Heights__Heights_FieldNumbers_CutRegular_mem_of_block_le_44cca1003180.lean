-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mem_of_block_le_44cca1003180
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mem_of_block_le_44cca1003180
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:54.390827+00:00
-- url     : https://prove2.me/theorems/b37df8bf-259f-41bc-804d-4ab3f93c1efa
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mem of block le 44cca1003180: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mem of block le 44cca1003180
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mem of block le 44cca1003180 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mem of block le 44cca1003180 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L67-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L67-L89

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mem_of_block_le_44cca1003180 {I : Ideal (MRing ι F)} {k : K}
    (hk : ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I) {m : K → ℕ} (hm : 1 ≤ m k)
    {f : MRing ι F} (hf : IsMultiHomog f m) : f ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«mem_of_block_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mem_of_block_le_44cca1003180
