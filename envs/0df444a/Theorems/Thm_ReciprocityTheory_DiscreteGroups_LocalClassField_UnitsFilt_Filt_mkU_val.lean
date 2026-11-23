-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_val
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.mkU_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:42.06933+00:00
-- url     : https://prove2.me/theorems/27c5d09e-4ef7-4104-9ba0-025d3c669881
-- title:
--   Filt: mk U val
-- statement:
--   The Filt construction uses the mk U val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandA.lean#L106-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandA.lean#L106-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.mkU_val (x : R) (hx : x ∈ I 0) : (h.mkU x hx : R) = 1 + x := by sorry
