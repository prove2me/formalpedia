-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_X_chartMap_017b67038871
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_X_chartMap_017b67038871
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:12.332056+00:00
-- url     : https://prove2.me/theorems/37e3ff49-bfb8-43b9-ae0e-634d7222e7b9
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel X chart Map 017b67038871: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel X chart Map 017b67038871
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel X chart Map 017b67038871 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel X chart Map 017b67038871 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L272-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L272-L274

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
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_X_chartMap_017b67038871 (i : ∀ k, ι k) (k' : K') :
    (X ⟨k', chartMap e σ hσ i k'⟩ : MRingOver F ι') = ren σ (X ⟨e.symm k', i (e.symm k')⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«X_chartMap» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_X_chartMap_017b67038871
