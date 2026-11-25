-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.liftNC_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:53.712865+00:00
-- url     : https://prove2.me/theorems/61f71721-ef40-43c9-8e93-ebe1d44ce639
-- title:
--   Tor: lift NC comp
-- statement:
--   The Tor construction uses the lift NC comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L101-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Splits.lean#L101-L123

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.liftNC_comp {A B C X ι' : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (b : Module.Basis ι' ℤ X) (v : ι' → Bˣ) (v' : ι' → Cˣ) (hv : ∀ k, (v' k).val = ρ (v k).val) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) ((Units.coeHom C).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v' k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f ((Units.coeHom B).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by sorry
