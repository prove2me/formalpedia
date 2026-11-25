-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:00.810809+00:00
-- url     : https://prove2.me/theorems/98c0725b-6905-4e87-babe-694b0c738025
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite trdeg hom Frac Deg Zero b6b3997ce745: P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite trdeg hom Frac Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite trdeg hom Frac Deg Zero b6b3997ce745 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite trdeg hom Frac Deg Zero b6b3997ce745 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L57-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
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
open GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
open IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745 (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«FunctionFieldFinite».«trdeg_homFracDegZero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745
