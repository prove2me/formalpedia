-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_trivial_inflation_h1_rat_mod_int_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h1_rat_mod_int_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:05:31.316901+00:00
-- url     : https://prove2.me/theorems/7def7e24-c3b9-4beb-a0b5-dbf85057c27d
-- title:
--   Local Class Field: trivial inflation h1 rat mod int injective
-- statement:
--   The Local Class Field construction uses the trivial inflation h1 rat mod int injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L125-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L125-L144

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h1_rat_mod_int_injective (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ QZ).hom.H 1) := by sorry
