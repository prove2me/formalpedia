-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:42.814513+00:00
-- url     : https://prove2.me/theorems/2aa0d632-3a59-44ed-9cd7-e51d51f6fb1f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor mem pull  6a8fb3a1b1a4: P2 M Reciprocity Theory Chart Restriction G Geo Tor mem pull  6a8fb3a1b1a4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor mem pull  6a8fb3a1b1a4 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor mem pull  6a8fb3a1b1a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L217-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L217-L220

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4 {x : X''} {J : PUnit → L.ι} : x ∈ (L.pull (F' ≫ F)).U J ↔ F (F' x) ∈ L.U (J PUnit.unit) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«mem_pull₂» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
