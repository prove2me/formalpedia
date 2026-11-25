-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_relDim_lt_of_lt_7832e8c64fa7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_relDim_lt_of_lt_7832e8c64fa7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:24.094251+00:00
-- url     : https://prove2.me/theorems/881d6193-73a8-5c56-a2a2-7d2a068d056c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral rel Dim lt of lt 7832e8c64fa7: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral rel Dim lt of lt 7832e8c64fa7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral rel Dim lt of lt 7832e8c64fa7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral rel Dim lt of lt 7832e8c64fa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L48-L57

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_relDim_lt_of_lt_7832e8c64fa7 {Q Q₂ : Ideal (MRing ι F)} [Q.IsPrime] [Q₂.IsPrime] (h : Q < Q₂) :
    relDim Q₂ < relDim Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalIntegral».«relDim_lt_of_lt» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_relDim_lt_of_lt_7832e8c64fa7
