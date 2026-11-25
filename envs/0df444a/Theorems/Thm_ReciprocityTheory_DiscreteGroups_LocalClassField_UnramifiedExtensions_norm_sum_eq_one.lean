-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sum_eq_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:41.288444+00:00
-- url     : https://prove2.me/theorems/6297cc45-5f2c-4775-8099-f95214dbab9d
-- title:
--   Unramified Extensions: norm sum eq one
-- statement:
--   The Unramified Extensions construction uses the norm sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L18-L36

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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_eq_one {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (b : ι → Obar p)
    (hb : ∀ j, (b j : PadicAlgCl p) ∈ K) (i : ι) (hi : b i = 1) :
    ‖∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ = 1 := by sorry
