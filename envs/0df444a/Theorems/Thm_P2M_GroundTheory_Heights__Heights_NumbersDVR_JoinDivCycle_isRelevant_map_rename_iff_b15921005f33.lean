-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isRelevant_map_rename_iff_b15921005f33
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isRelevant_map_rename_iff_b15921005f33
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:04:52.500056+00:00
-- url     : https://prove2.me/theorems/99d9d981-a0f3-5208-a730-c266fc99bfe0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Relevant map rename iff b15921005f33: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Relevant map rename iff b15921
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Relevant map rename iff b15921005f33 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Relevant map rename iff b15921005f33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L103-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L103-L128

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isRelevant_map_rename_iff_b15921005f33 (Q : Ideal (MRing ι R)) (hQ : Q ≠ ⊤) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (Q.map ε) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«isRelevant_map_rename_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isRelevant_map_rename_iff_b15921005f33
