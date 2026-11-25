-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_normL
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.normL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:48.090109+00:00
-- url     : https://prove2.me/theorems/b6b28092-2dea-4789-a217-830085ba94dd
-- title:
--   Tor: norm L
-- statement:
--   The Tor construction uses the norm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L81-L89

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.normL {S Y Z : Scheme.{0}} (e₁ : S ⟶ Y) (e₂ : S ⟶ Z) (a : Z ⟶ Y) (he : e₂ ≫ a = e₁) (W : Y.Opens) (V : S.Opens)
    (u : Γ(Y, W)ˣ) (r : Γ(S, V)ˣ)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) * res inf_le_right r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ (a ⁻¹ᵁ W) ⊓ V ≤ e₂ ⁻¹ᵁ (a ⁻¹ᵁ W)) (pullU e₂ _ (pullU a W u)) * res inf_le_right r = 1 := by sorry
