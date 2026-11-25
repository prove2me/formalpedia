-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:51.920329+00:00
-- url     : https://prove2.me/theorems/b03807da-07a1-4cfe-80e8-f5a4a756a3b2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular colon eq of not mem 041a78df4446: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular colon eq of not mem 041a78df4446
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular colon eq of not mem 041a78df4446 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular colon eq of not mem 041a78df4446 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L125-L129

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446 {P : Ideal (MRing ι F)} [hP : P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«colon_eq_of_not_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446
