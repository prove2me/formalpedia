-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_cycEval_map_87059aec3247
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_cycEval_map_87059aec3247
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:41.540285+00:00
-- url     : https://prove2.me/theorems/c7d052eb-e24c-463b-aa5a-3bc5295971db
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel cyc Eval map 87059aec3247: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel cyc Eval map 87059aec3247
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel cyc Eval map 87059aec3247 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel cyc Eval map 87059aec3247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L248-L253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ
omit hσ
omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_cycEval_map_87059aec3247 (J : Ideal (MRingOver F ι') → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (Finsupp.equivMapDomain (idealEquiv σ) D) = cycEval (fun W => J (idealEquiv σ W)) D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«cycEval_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_cycEval_map_87059aec3247
