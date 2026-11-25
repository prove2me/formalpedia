-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:17.969407+00:00
-- url     : https://prove2.me/theorems/a801b5ca-5adb-4043-b86d-07737c24a744
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order One is Weighted Homogeneous multi Cone Map 4a037a706f8f: P2 M Ground Theory Heights  Heights Inter Diagonal Order One is Weighted Homogeneous m
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order One is Weighted Homogeneous multi Cone Map 4a037a706f8f construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order One is Weighted Homogeneous multi Cone Map 4a037a706f8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L78-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f (c : (Σ k, ι k) → Φ) {p : MRing ι} {m : K → ℕ}
    (hp : IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) p m) :
    IsWeightedHomogeneous (fun k : K => (Pi.single k 1 : K → ℕ)) (T.multiConeMap c p) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrderOne».«isWeightedHomogeneous_multiConeMap» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f
