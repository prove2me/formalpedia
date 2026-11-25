-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_contract_le_061fb5b3ca5f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_contract_le_061fb5b3ca5f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:52.362812+00:00
-- url     : https://prove2.me/theorems/0004b29c-a98a-4ee2-8724-016d64be09f2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral contract le 061fb5b3ca5f: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral contract le 061fb5b3ca5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral contract le 061fb5b3ca5f construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Integral contract le 061fb5b3ca5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L68-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean#L68-L103

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
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_contract_le_061fb5b3ca5f {P' : Ideal (MRing ι' F)} [P'.IsPrime] {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hPW : contractPrime j P' ≤ W) (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R)
    {y : Ideal (MRing ι' F)} (hy : IsMultiProjPrime y) (hP'y : P' ≤ y)
    (hcen : ∀ (b : K' → ℕ) (f g : MRing ι' F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' f) /
          algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
            (Ideal.Quotient.mk P' f) / algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈
          R.nonunits)) :
    contractPrime j y ≤ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalIntegral».«contract_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_contract_le_061fb5b3ca5f
