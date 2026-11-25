-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_smul_prod_univ
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.smul_prod_univ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:54.04147+00:00
-- url     : https://prove2.me/theorems/51b5bd14-83f4-45b2-b667-e7245d9abc4c
-- title:
--   Units Filt: smul prod univ
-- statement:
--   The Units Filt construction uses the smul prod univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandB.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandB.lean#L21-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
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
variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.smul_prod_univ (g : G) (x : R) : g • ∏ g' : G, g' • x = ∏ g' : G, g' • x := by sorry
