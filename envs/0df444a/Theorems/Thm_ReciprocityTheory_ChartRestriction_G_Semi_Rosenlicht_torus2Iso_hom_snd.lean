-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Iso_hom_snd
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Iso_hom_snd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:38.507353+00:00
-- url     : https://prove2.me/theorems/2a8568b0-344c-4d68-a309-80f02c60e8e3
-- title:
--   Rosenlicht: torus2 Iso hom snd
-- statement:
--   The Rosenlicht construction uses the torus2 Iso hom snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L412-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L412-L419

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Iso_hom_snd : (torus2Iso K X).hom ≫
    (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) ≫
          (torusIso K X).hom := by sorry
