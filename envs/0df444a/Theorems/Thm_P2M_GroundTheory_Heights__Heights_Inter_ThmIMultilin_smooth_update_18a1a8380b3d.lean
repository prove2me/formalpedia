-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:19.255788+00:00
-- url     : https://prove2.me/theorems/1e1bf4b4-6303-481a-8bf2-5fc5ee628e70
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IMultilin smooth update 18a1a8380b3d: P2 M Ground Theory Heights  Heights Inter Thm IMultilin smooth update 18a1a8380b3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IMultilin smooth update 18a1a8380b3d construction uses the P2 M Ground Theory Heights  Heights Inter Thm IMultilin smooth update 18a1a8380b3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIMultilin.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIMultilin.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIMultilin».«smooth_update» := P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d
