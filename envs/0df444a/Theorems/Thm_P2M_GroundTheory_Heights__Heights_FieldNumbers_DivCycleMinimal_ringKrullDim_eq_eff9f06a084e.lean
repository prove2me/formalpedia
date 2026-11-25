-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:52:35.89621+00:00
-- url     : https://prove2.me/theorems/426c8b6f-76ea-4d89-b67b-e2ccdab77e4e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Div Cycle Minimal ring Krull Dim eq eff9f06a084e: P2 M Ground Theory Heights  Heights Field Numbers Div Cycle Minimal ring Krull Dim eq eff9f06a084e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Div Cycle Minimal ring Krull Dim eq eff9f06a084e construction uses the P2 M Ground Theory Heights  Heights Field Numbers Div Cycle Minimal ring Krull Dim eq eff9f06a084e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivCycleMinimal.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivCycleMinimal.lean#L16-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleMinimal
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«DivCycleMinimal».«ringKrullDim_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e
