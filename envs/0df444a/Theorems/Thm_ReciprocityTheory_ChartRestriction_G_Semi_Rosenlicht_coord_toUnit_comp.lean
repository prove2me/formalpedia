-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_toUnit_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_toUnit_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:50.445167+00:00
-- url     : https://prove2.me/theorems/a50eedad-f31b-4435-bb07-b281333892d5
-- title:
--   Rosenlicht: coord to Unit comp
-- statement:
--   The Rosenlicht construction uses the coord to Unit comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L193-L200

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable {S : Scheme.{u}}

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_toUnit_comp (Z : Over S) {Y : Type u} [AddCommGroup Y]
    (e : 𝟙_ (Over S) ⟶ splitTorus S Y) (x : torusRing ZU Y) :
    (coord (toUnit Z ≫ e)).hom x = Z.hom.appTop.hom ((coord e).hom x) := by sorry
