-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isPrime_map_4e84efccef29
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isPrime_map_4e84efccef29
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:56.30079+00:00
-- url     : https://prove2.me/theorems/f5131e1f-56b0-45ce-a9cb-42dd8ccd3e21
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Prime map 4e84efccef29: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Prime map 4e84efccef29
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Prime map 4e84efccef29 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Prime map 4e84efccef29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L32-L34

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isPrime_map_4e84efccef29 (W : Ideal R) [W.IsPrime] : (W.map (φ : R →+* R')).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«isPrime_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isPrime_map_4e84efccef29
