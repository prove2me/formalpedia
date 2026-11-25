-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_id_torusGamma
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_id_torusGamma
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:55.447806+00:00
-- url     : https://prove2.me/theorems/3eec6272-f718-546c-a11a-9f102d895c8b
-- title:
--   Rosenlicht: coord id torus Gamma
-- statement:
--   The Rosenlicht construction uses the coord id torus Gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L287-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L287-L295

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_id_torusGamma :
    coord (𝟙 (splitTorus (Spec (.of K)) X)) ≫ torusGamma K X =
      CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X)) := by sorry
