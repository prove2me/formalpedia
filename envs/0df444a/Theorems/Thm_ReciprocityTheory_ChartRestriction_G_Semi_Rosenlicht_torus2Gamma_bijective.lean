-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Gamma_bijective
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Gamma_bijective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:46.369209+00:00
-- url     : https://prove2.me/theorems/568518cf-8966-5520-a435-c705988b69b2
-- title:
--   Rosenlicht: torus2 Gamma bijective
-- statement:
--   The Rosenlicht construction uses the torus2 Gamma bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L426-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean#L426-L432

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Gamma_bijective : Function.Bijective (torus2Gamma K X).hom := by sorry
