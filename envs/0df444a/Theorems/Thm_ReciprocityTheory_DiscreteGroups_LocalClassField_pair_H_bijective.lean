-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pair_H_bijective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.pair_H_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:52.462502+00:00
-- url     : https://prove2.me/theorems/33a77c77-5cdd-58ea-a289-211388f2c53d
-- title:
--   Local Class Field: pair H bijective
-- statement:
--   The Local Class Field construction uses the pair H bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfResEqZeroOfCoprime.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfResEqZeroOfCoprime.lean#L18-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.pair_H_bijective {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) := by sorry
