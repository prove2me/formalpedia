-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_comap_map_rename_0a31300effaa
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_comap_map_rename_0a31300effaa
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:42.37016+00:00
-- url     : https://prove2.me/theorems/d7f9c061-d16f-4b83-9e34-d70b23bb9820
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle comap map rename 0a31300effaa: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle comap map rename 0a31300effaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle comap map rename 0a31300effaa construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle comap map rename 0a31300effaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L78-L80

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_comap_map_rename_0a31300effaa (I : Ideal (MRing ι R)) : (I.map ε).comap ε = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«comap_map_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_comap_map_rename_0a31300effaa
