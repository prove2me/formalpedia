-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:07.76008+00:00
-- url     : https://prove2.me/theorems/58b65b4d-ab8a-47e6-8d16-d49824282332
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim lt top f6ad9b5ae3d3: P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim lt top f6ad9b5ae3d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim lt top f6ad9b5ae3d3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted ring Krull Dim lt top f6ad9b5ae3d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean#L26-L30

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3 [Finite K] [∀ k, Finite (ι k)] (Q : Ideal (MRing ι F)) :
    ringKrullDim (MRing ι F ⧸ Q) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«ringKrullDim_lt_top» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3
