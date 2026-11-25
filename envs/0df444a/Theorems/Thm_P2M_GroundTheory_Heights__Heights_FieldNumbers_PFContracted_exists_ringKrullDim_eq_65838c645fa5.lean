-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:22.116838+00:00
-- url     : https://prove2.me/theorems/c1324664-01b3-49e2-aaff-1aba91c636b2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted exists ring Krull Dim eq 65838c645fa5: P2 M Ground Theory Heights  Heights Field Numbers PFContracted exists ring Krull Dim eq 65838c645f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted exists ring Krull Dim eq 65838c645fa5 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted exists ring Krull Dim eq 65838c645fa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L141-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L141-L160

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5 [Fintype K] [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι F)}
    [Q.IsPrime] (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q)
    (hrel : IsRelevant Q) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRing ι F ⧸ Q) = D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«exists_ringKrullDim_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
