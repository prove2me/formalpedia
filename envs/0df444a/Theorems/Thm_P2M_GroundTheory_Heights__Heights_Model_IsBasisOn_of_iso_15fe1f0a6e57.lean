-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:40.841806+00:00
-- url     : https://prove2.me/theorems/66f3db80-610a-4428-b328-26bec189ede0
-- title:
--   P2 M Ground Theory Heights  Heights Model Is Basis On of iso 15fe1f0a6e57: P2 M Ground Theory Heights  Heights Model Is Basis On of iso 15fe1f0a6e57
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Is Basis On of iso 15fe1f0a6e57 construction uses the P2 M Ground Theory Heights  Heights Model Is Basis On of iso 15fe1f0a6e57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L421-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L421-L432

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
universe u
variable {X Y : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57 {M N : X.Modules} (e : M ≅ N) {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    IsBasisOn N U (fun i => (e.hom.app U).hom (s i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsBasisOn».«of_iso» := P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
