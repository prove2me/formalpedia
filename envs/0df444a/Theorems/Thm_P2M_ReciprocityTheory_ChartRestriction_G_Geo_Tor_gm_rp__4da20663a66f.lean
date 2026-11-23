-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:51.848797+00:00
-- url     : https://prove2.me/theorems/ccefb8e0-2907-4852-ae2b-88e6bc93e68a
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  4da20663a66f: P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  4da20663a66f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  4da20663a66f construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  4da20663a66f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L30-L33

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens)
    (hle : V ≤ b ⁻¹ᵁ (a ⁻¹ᵁ U)) (hz : z ∈ V) (u : Γ(X, U)ˣ) :
    gm (𝟙 Z) z V (res hle (pullU b (a ⁻¹ᵁ U) (pullU a U u))) = gm (b ≫ a) z U u := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«gm_rp₂» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f
