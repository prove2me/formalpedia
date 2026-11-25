-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:55.618379+00:00
-- url     : https://prove2.me/theorems/0f1a1811-538e-4b82-b4ed-2eed0f8441be
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular is Multi Homog Ideal sup span 9559967f1914: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular is Multi Homog Ideal sup span 95
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular is Multi Homog Ideal sup span 9559967f1914 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular is Multi Homog Ideal sup span 9559967f1914 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L110-L121

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914 {P : Ideal (MRing ι F)} (hP : IsMultiHomogIdeal P)
    {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914
