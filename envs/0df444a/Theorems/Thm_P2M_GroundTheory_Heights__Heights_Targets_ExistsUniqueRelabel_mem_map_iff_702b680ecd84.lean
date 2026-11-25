-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:29.84227+00:00
-- url     : https://prove2.me/theorems/447911aa-fd62-437e-810f-6e3a029adb1f
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem map iff 702b680ecd84: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem map iff 702b680ecd84
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem map iff 702b680ecd84 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem map iff 702b680ecd84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L18-L19

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
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84 (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«mem_map_iff» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
