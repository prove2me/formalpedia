-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.mk_eq_mk_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:38.470863+00:00
-- url     : https://prove2.me/theorems/dcc71d9c-6f0d-4d11-8a8b-9ce89921b62a
-- title:
--   Herbrand: mk eq mk iff
-- statement:
--   The Herbrand construction uses the mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L31-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.mk_eq_mk_iff {D N : M →+ M} (x y : D.ker) :
    (QuotientAddGroup.mk x : T D N) = QuotientAddGroup.mk y ↔ (x : M) - y ∈ N.range := by sorry
