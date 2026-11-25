-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_adm
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.adm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:01.941809+00:00
-- url     : https://prove2.me/theorems/ed068ec3-5310-4143-ae8b-9dd1f7e303fb
-- title:
--   Kummer: adm
-- statement:
--   The Kummer construction uses the adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L50-L54

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
open ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
variable {p n}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.adm {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : admitted (iP K hζ) (pP p K n) := by sorry
