-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_kbarRep_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.kbarRep_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:44.378601+00:00
-- url     : https://prove2.me/theorems/cc743c0b-6fa0-4d2f-abfe-434416cc3636
-- title:
--   Kummer: kbar Rep apply
-- statement:
--   The Kummer construction uses the kbar Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KummerA.lean#L59-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
open _root_.Neutral.B1
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.kbarRep_apply (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := by sorry
