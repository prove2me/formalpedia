-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:51.432795+00:00
-- url     : https://prove2.me/theorems/c55e2139-1910-4adb-a21e-d30118a59790
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt coord mem e0cbe1c6e1f6: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt coord mem e0cbe1c6e1f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt coord mem e0cbe1c6e1f6 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt coord mem e0cbe1c6e1f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L35-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6 (u : T) : y ⟨(), u⟩ ∈ chartLat y 1 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«coord_mem» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
