-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusIso_hom_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torusIso_hom_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:00.217805+00:00
-- url     : https://prove2.me/theorems/9e926509-14aa-40f0-94bb-23101760a266
-- title:
--   Rosenlicht: torus Iso hom fst
-- statement:
--   The Rosenlicht construction uses the torus Iso hom fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L264-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L264-L268

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
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torusIso_hom_fst : (torusIso K X).hom ≫ torusFst (Spec (.of K)) X =
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))) := by sorry
