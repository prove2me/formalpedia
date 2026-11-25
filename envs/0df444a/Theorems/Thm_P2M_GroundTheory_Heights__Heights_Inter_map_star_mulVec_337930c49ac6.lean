-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_map_star_mulVec_337930c49ac6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_map_star_mulVec_337930c49ac6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:23.426629+00:00
-- url     : https://prove2.me/theorems/76815ccc-ca50-4c53-8a61-aa2399900531
-- title:
--   P2 M Ground Theory Heights  Heights Inter map star mul Vec 337930c49ac6: P2 M Ground Theory Heights  Heights Inter map star mul Vec 337930c49ac6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter map star mul Vec 337930c49ac6 construction uses the P2 M Ground Theory Heights  Heights Inter map star mul Vec 337930c49ac6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFIntZero.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFIntZero.lean#L61-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFIntZero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_map_star_mulVec_337930c49ac6 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«map_star_mulVec» := P2M_GroundTheory_Heights__Heights_Inter_map_star_mulVec_337930c49ac6
