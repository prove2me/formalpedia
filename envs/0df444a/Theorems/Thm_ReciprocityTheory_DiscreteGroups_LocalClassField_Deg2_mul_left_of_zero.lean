-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_mul_left_of_zero
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.mul_left_of_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:07.791094+00:00
-- url     : https://prove2.me/theorems/fe9a698b-c298-49db-a5d2-e3d9e602b7d3
-- title:
--   Deg2: mul left of zero
-- statement:
--   The Deg2 construction uses the mul left of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/IsTwoCocycleCoboundary.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/IsTwoCocycleCoboundary.lean#L47-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)
variable {ρ}
variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)
include hc

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.mul_left_of_zero (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (n : G) (hn : n ∈ N) (g h : G) :
    c (n * g) h = ρ n (c g h) := by sorry
