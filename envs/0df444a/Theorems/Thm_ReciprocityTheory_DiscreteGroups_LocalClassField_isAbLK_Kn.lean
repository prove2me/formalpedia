-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isAbLK_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isAbLK_Kn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:46.764882+00:00
-- url     : https://prove2.me/theorems/235aa204-70d0-4b1e-b7c2-8436635aeb72
-- title:
--   Local Class Field: is Ab LK Kn
-- statement:
--   The Local Class Field construction uses the is Ab LK Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L64-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
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
open Topology
open scoped commutatorElement
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isAbLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : IsAbLK p K (Kn p K n) := by sorry
