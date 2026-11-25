-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:53.159437+00:00
-- url     : https://prove2.me/theorems/e2d8b2e0-e4d4-5303-891d-9026d4c2b8fb
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor lift NC comp  de63461cc6c3: P2 M Reciprocity Theory Chart Restriction G Geo Tor lift NC comp  de63461cc6c3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor lift NC comp  de63461cc6c3 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor lift NC comp  de63461cc6c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L91-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3 {A B C X : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (g : Multiplicative X →* B) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) (ρ.toMonoidHom.comp g) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«liftNC_comp₀» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3
