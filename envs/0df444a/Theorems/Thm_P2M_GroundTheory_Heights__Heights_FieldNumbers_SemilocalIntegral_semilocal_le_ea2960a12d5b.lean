-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_semilocal_le_ea2960a12d5b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_semilocal_le_ea2960a12d5b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:53:59.688802+00:00
-- url     : https://prove2.me/theorems/bff42588-7e87-438e-be9c-9547b3a9ba4b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral semilocal le ea2960a12d5b: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral semilocal le ea2960a12d5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral semilocal le ea2960a12d5b construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral semilocal le ea2960a12d5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L105-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L105-L150

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
variable {F : Type u} [Field F] {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] {j : K ↪ K'} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_semilocal_le_ea2960a12d5b (hC : ValuativeCentre.Statement.{u}) {P' : Ideal (MRing ι' F)} [P'.IsPrime]
    (hP' : IsMultiProjPrime P') {n : ℕ} (hP'n : relDim P' = (n + 1 : ℕ))
    (hPn : relDim (contractPrime j P') = (n + 1 : ℕ)) {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hW : IsMultiProjPrime W) (hWn : relDim W = (n : ℕ)) (hPW : contractPrime j P' ≤ W)
    (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R) :
    ∀ x ∈ degZeroLoc P' (fibrePrimes j P' W), x ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalIntegral».«semilocal_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_semilocal_le_ea2960a12d5b
