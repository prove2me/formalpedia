-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_sub_toLinearMap
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.sub_toLinearMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:01.433827+00:00
-- url     : https://prove2.me/theorems/42c7767e-97a6-495e-a52a-a82235f53bc3
-- title:
--   Local Class Field: sub to Linear Map
-- statement:
--   The Local Class Field construction uses the sub to Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L158-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L158-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsLowExists
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh CategoryTheory
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.sub_toLinearMap (M : TRep R C) (g : C) :
    (Rep.applyAsHom (Rep.of M.rho) g - 𝟙 (Rep.of M.rho)).hom.toLinearMap = M.rho g - LinearMap.id := by sorry
