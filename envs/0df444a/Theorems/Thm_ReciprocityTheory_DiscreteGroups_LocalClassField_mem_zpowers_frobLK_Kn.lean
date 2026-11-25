-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_zpowers_frobLK_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_zpowers_frobLK_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:03.212781+00:00
-- url     : https://prove2.me/theorems/e7c371bd-f21a-4234-a26e-daea9efa7e72
-- title:
--   Local Class Field: mem zpowers frob LK Kn
-- statement:
--   The Local Class Field construction uses the mem zpowers frob LK Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L201-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
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
variable {p K}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_zpowers_frobLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    (g : GalLK p K (Kn p K n)) : g ∈ Subgroup.zpowers (frobLK p K (Kn p K n)) := by sorry
