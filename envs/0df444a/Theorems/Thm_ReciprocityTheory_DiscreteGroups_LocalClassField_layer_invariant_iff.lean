-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_layer_invariant_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.layer_invariant_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:17.747425+00:00
-- url     : https://prove2.me/theorems/1dbf5a29-4ec8-4f20-bc13-35e17b57a384
-- title:
--   Local Class Field: layer invariant iff
-- statement:
--   The Local Class Field construction uses the layer invariant iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L254-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L254-L262

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.layer_invariant_iff [(subG p K L).Normal] (x : (layer p K L).V) :
    (∀ g, (layer p K L).rho g x = x) ↔ x.1 ∈ multOf p K := by sorry
