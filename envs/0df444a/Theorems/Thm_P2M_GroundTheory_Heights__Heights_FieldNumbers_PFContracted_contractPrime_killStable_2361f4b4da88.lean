-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:03.006419+00:00
-- url     : https://prove2.me/theorems/58be210b-76e5-4cd3-94c5-e0de6c28a0e3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted contract Prime kill Stable 2361f4b4da88: P2 M Ground Theory Heights  Heights Field Numbers PFContracted contract Prime kill Stable 2361f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted contract Prime kill Stable 2361f4b4da88 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted contract Prime kill Stable 2361f4b4da88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L188-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88 (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (hP' : IsMultiHomogIdeal P') (T : Finset K) (q : MRing (fun k => ι' (j k)) F)
    (hq : q ∈ contractPrime j P') : killBlocks T q ∈ contractPrime j P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«contractPrime_killStable» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
