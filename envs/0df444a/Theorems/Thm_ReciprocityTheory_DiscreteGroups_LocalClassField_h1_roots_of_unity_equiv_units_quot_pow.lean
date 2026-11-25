-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h1_roots_of_unity_equiv_units_quot_pow
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.h1_roots_of_unity_equiv_units_quot_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:56.275635+00:00
-- url     : https://prove2.me/theorems/8171e1ea-3234-4e6c-aaa9-21bf107ddd50
-- title:
--   Local Class Field: h1 roots of unity equiv units quot pow
-- statement:
--   The Local Class Field construction uses the h1 roots of unity equiv units quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Kummer.lean#L127-L129

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
open Kummer

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.h1_roots_of_unity_equiv_units_quot_pow (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by sorry
