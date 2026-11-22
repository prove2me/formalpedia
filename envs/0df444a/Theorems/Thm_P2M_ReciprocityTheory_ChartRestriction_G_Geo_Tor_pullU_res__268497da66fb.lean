-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:26.169065+00:00
-- url     : https://prove2.me/theorems/bb3d7c95-ee4f-4a09-a1aa-a771aee37f20
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor pull U res  268497da66fb: P2 M Reciprocity Theory Chart Restriction G Geo Tor pull U res  268497da66fb
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor pull U res  268497da66fb construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor pull U res  268497da66fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L18-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) :
    pullU f V (res h u) = res (f.preimage_mono h) (pullU f U u) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«pullU_res₂» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
