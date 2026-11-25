-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_mem_map_rename_iff_8e800919efe0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_mem_map_rename_iff_8e800919efe0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:00:19.748197+00:00
-- url     : https://prove2.me/theorems/0edc5b0f-e546-5e80-ac90-cf94bd29af75
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle rename mem map rename iff 8e800919efe0: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle rename mem map rename iff 8e800919
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle rename mem map rename iff 8e800919efe0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle rename mem map rename iff 8e800919efe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L75-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)
local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_mem_map_rename_iff_8e800919efe0 (I : Ideal (MRing ι R)) (x : MRing ι R) : ε x ∈ I.map ε ↔ x ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«rename_mem_map_rename_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_rename_mem_map_rename_iff_8e800919efe0
