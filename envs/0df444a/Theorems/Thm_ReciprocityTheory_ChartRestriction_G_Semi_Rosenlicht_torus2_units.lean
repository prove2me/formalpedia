-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2_units
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2_units
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:44.155648+00:00
-- url     : https://prove2.me/theorems/1701be8c-5a5c-5d85-8d01-407da26b203d
-- title:
--   Rosenlicht: torus2 units
-- statement:
--   The Rosenlicht construction uses the torus2 units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L466-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L466-L502

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2_units [TwoUniqueSums X]
    {w : Γ((splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left, ⊤)} (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a b : X), IsUnit c ∧
      w = (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          ((splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a) *
        (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          (chi X b) := by sorry
