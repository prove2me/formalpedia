-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_layer_val_mem
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.layer_val_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:49.017712+00:00
-- url     : https://prove2.me/theorems/8744bf2d-3f8d-492b-a2da-4ad16b60930e
-- title:
--   Local Class Field: layer val mem
-- statement:
--   The Local Class Field construction uses the layer val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L251-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L251-L252

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.layer_val_mem [(subG p K L).Normal] (h : K ≤ L) (x : (layer p K L).V) : x.1 ∈ multOf p L := by sorry
