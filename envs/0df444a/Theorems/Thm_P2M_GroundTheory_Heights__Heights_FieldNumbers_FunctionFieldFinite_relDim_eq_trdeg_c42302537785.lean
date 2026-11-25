-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:52:01.641867+00:00
-- url     : https://prove2.me/theorems/4c59599b-0f12-5088-8cd6-a0599dca33d9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite rel Dim eq trdeg c42302537785: P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite rel Dim eq trdeg c4230253
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite rel Dim eq trdeg c42302537785 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite rel Dim eq trdeg c42302537785 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L66-L83

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785 (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«FunctionFieldFinite».«relDim_eq_trdeg» := P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785
