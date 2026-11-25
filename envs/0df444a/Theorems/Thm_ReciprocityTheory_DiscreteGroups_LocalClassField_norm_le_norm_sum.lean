-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_le_norm_sum
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_le_norm_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:52.1736+00:00
-- url     : https://prove2.me/theorems/ca2b4df6-424b-4336-905e-253f2786961a
-- title:
--   Local Class Field: norm le norm sum
-- statement:
--   The Local Class Field construction uses the norm le norm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L40-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L40-L62

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_le_norm_sum {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (a : ι → K) (i : ι) :
    ‖(a i : PadicAlgCl p)‖ ≤ ‖∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ := by sorry
