-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:03:38.491178+00:00
-- url     : https://prove2.me/theorems/c66ea6c2-2fea-53a3-8ec7-295c2f01305a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular rel Dim eq nat Cast iff cb89d927b72d: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular rel Dim eq nat Cast iff cb89d927b72d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular rel Dim eq nat Cast iff cb89d927b72d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular rel Dim eq nat Cast iff cb89d927b72d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L133-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L133-L163

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d [Fintype K] (I : Ideal (MRing ι F)) (d : ℕ) :
    relDim I = ((d : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MRing ι F ⧸ I) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«relDim_eq_natCast_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d
