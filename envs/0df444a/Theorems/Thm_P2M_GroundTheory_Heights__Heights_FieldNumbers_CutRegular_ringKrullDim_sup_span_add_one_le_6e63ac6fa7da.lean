-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:58.984127+00:00
-- url     : https://prove2.me/theorems/d167369c-4bac-484d-b2b8-fbe788351706
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim sup span add one le 6e63ac6fa7da: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim sup span add
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim sup span add one le 6e63ac6fa7da construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular ring Krull Dim sup span add one le 6e63ac6fa7da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L206-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L206-L217

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«ringKrullDim_sup_span_add_one_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da
