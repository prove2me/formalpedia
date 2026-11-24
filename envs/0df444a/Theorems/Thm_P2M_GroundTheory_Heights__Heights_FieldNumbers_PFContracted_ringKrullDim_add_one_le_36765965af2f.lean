-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:16.962814+00:00
-- url     : https://prove2.me/theorems/26dfbb74-b9b2-4970-8be7-cffb59ffbdb2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim add one le 36765965af2f: P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim add one le 36765965
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim add one le 36765965af2f construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim add one le 36765965af2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«ringKrullDim_add_one_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
