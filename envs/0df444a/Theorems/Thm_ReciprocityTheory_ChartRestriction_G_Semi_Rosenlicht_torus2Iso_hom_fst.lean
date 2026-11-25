-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Iso_hom_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Iso_hom_fst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:41.636062+00:00
-- url     : https://prove2.me/theorems/991c55b7-e0ad-4b3c-83d8-78f76431098d
-- title:
--   Rosenlicht: torus2 Iso hom fst
-- statement:
--   The Rosenlicht construction uses the torus2 Iso hom fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L404-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L404-L410

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Iso_hom_fst : (torus2Iso K X).hom ≫
    (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≫ (torusIso K X).hom := by sorry
