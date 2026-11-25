-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_RationalModIntegerChains_qz_torsion
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains.qz_torsion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:08.930335+00:00
-- url     : https://prove2.me/theorems/8d2b941f-2d9f-449c-9444-4e260de31ce1
-- title:
--   Rational Mod Integer Chains: qz torsion
-- statement:
--   The Rational Mod Integer Chains construction uses the qz torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemZmultiplesOfAddOrderOf.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemZmultiplesOfAddOrderOf.lean#L45-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
open ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains
open scoped Nat
variable {A : Type} [AddCommGroup A]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains.qz_torsion (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by sorry
