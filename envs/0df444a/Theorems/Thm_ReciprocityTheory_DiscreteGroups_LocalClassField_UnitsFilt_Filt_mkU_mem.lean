-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_mem
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.mkU_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:06.493995+00:00
-- url     : https://prove2.me/theorems/fe1daa7b-a1f4-43b8-934a-b99f256ae891
-- title:
--   Filt: mk U mem
-- statement:
--   The Filt construction uses the mk U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandA.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandA.lean#L108-L109

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.mkU_mem {n : ℕ} (x : R) (hx : x ∈ I n) : h.mkU x (h.le_zero n hx) ∈ h.V n := by sorry
