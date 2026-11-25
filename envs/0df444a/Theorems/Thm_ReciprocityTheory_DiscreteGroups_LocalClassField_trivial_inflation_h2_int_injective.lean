-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_trivial_inflation_h2_int_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h2_int_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:10.655108+00:00
-- url     : https://prove2.me/theorems/78e3a36d-6d8c-41ae-8a04-d292a52a6894
-- title:
--   Local Class Field: trivial inflation h2 int injective
-- statement:
--   The Local Class Field construction uses the trivial inflation h2 int injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L146-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L146-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h2_int_injective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [CompactSpace G']
    [T2Space G'] [TotallyDisconnectedSpace G'] (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ ℤ).hom.H 2) := by sorry
