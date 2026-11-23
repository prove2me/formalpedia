-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:21.399816+00:00
-- url     : https://prove2.me/theorems/13c833f1-4b34-4e1e-bf0f-37a8f2ee629f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  e27165827f88: P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  e27165827f88
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  e27165827f88 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor gm rp  e27165827f88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L27-L28

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88 {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U) (hz : z ∈ V)
    (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«gm_rp₁» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
