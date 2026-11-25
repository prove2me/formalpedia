-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_comp_appTop
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.toUnit_comp_appTop
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:27.757684+00:00
-- url     : https://prove2.me/theorems/a1fdbfc6-0c10-5a9f-ad02-b1ca945f1d3a
-- title:
--   Rosenlicht: to Unit comp app Top
-- statement:
--   The Rosenlicht construction uses the to Unit comp app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L187-L191

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.toUnit_comp_appTop (Z : Over S) {V : Over S} (e : 𝟙_ (Over S) ⟶ V) (x : Γ(V.left, ⊤)) :
    (toUnit Z ≫ e).left.appTop.hom x = Z.hom.appTop.hom (e.left.appTop.hom x) := by sorry
