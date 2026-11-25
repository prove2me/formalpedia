-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:34.041642+00:00
-- url     : https://prove2.me/theorems/2d02c827-ca87-5d27-9a1c-55f2dde5b4c0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map contract coe ebf358cf7871: P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map contract coe ebf358cf78
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map contract coe ebf358cf7871 construction uses the P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map contract coe ebf358cf7871 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLoc.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLoc.lean#L68-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
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
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871 (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«degZeroLoc».«algebraMap_contract_coe» := P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871
