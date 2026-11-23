-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.prod_fam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:29.299101+00:00
-- url     : https://prove2.me/theorems/cd57e6b5-e3e8-4db1-a832-cf0c0d440758
-- title:
--   DVR: prod fam
-- statement:
--   The DVR construction uses the prod fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L64-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.prod_fam {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ DegPre.famφ D F α i) ^ DegPre.famε k i =
      h (ρ ≫ DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (cP D T α * (ρ ≫ DegPre.prB D F)).left * (h (cP D T α).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left := by sorry
