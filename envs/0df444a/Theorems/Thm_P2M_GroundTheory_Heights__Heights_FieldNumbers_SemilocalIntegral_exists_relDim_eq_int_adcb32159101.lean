-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_relDim_eq_int_adcb32159101
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_relDim_eq_int_adcb32159101
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:53:45.893457+00:00
-- url     : https://prove2.me/theorems/d170b8ef-3cd7-47d3-bcbb-b95c0331a92c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists rel Dim eq int adcb32159101: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists rel Dim eq int adcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists rel Dim eq int adcb32159101 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists rel Dim eq int adcb32159101 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L43-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
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
open GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_relDim_eq_int_adcb32159101 (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ d : ℤ, relDim Q = ((d : WithTop ℤ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalIntegral».«exists_relDim_eq_int» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_relDim_eq_int_adcb32159101
