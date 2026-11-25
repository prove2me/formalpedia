-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_splitTorus_rigidity
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.splitTorus_rigidity
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:52.861236+00:00
-- url     : https://prove2.me/theorems/7d249354-d242-41c9-833c-4012a86df46d
-- title:
--   Semi: split Torus rigidity
-- statement:
--   The Semi construction uses the split Torus rigidity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L520-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L520-L585

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
open Rosenlicht

theorem ReciprocityTheory.ChartRestriction.G.Semi.splitTorus_rigidity (K : Type u) [Field K] (X : Type u) [AddCommGroup X] [TwoUniqueSums X]
    (Y : Type u) [AddCommGroup Y]
    (f : splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X ⟶ splitTorus (Spec (.of K)) Y)
    (h1 : lift (𝟙 _) (toUnit _ ≫ η) ≫ f = toUnit _ ≫ η)
    (h2 : lift (toUnit _ ≫ η) (𝟙 _) ≫ f = toUnit _ ≫ η) :
    f = toUnit _ ≫ η := by sorry
