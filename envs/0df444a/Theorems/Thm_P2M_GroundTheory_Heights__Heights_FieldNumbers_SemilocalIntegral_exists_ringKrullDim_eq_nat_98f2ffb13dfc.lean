-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:34.446578+00:00
-- url     : https://prove2.me/theorems/61a6c125-5a70-5aea-b2e6-82a2b36e72c8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists ring Krull Dim eq nat 98f2ffb13dfc: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists ring Krull D
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists ring Krull Dim eq nat 98f2ffb13dfc construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral exists ring Krull Dim eq nat 98f2ffb13dfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L28-L41

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalIntegral».«exists_ringKrullDim_eq_nat» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc
