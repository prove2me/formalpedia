-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_proof_e9bfb864d7e9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_proof_e9bfb864d7e9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:18.247605+00:00
-- url     : https://prove2.me/theorems/cf84b854-e260-5543-a847-5ed4a1c02627
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular proof e9bfb864d7e9: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular proof e9bfb864d7e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular proof e9bfb864d7e9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular proof e9bfb864d7e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L249-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L249-L311

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumAdd_proof_059e7dc472f4

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
open CutRegular

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_proof_e9bfb864d7e9 (h1 : HilbExactDivide.Statement.{u}) (h2 : MultEqualsCoeff.Statement.{u})
    (_h3 : IntNumSymm.Statement.{u}) : CutRegular.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_proof_e9bfb864d7e9
