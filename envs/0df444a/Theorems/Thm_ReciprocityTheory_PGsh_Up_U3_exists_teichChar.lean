-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_exists_teichChar
-- name    : ReciprocityTheory.PGsh.Up.U3.exists_teichChar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:15.523126+00:00
-- url     : https://prove2.me/theorems/cb26cd9e-9399-40be-8cec-5b20b3a50e12
-- title:
--   U3: exists teich Char
-- statement:
--   The U3 construction uses the exists teich Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L156-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L156-L210

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.U3.exists_teichChar [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) :
    ∃ ω : ZMod p → C, (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      ω 0 = 0 ∧ ω 1 = 1 ∧ (∀ a b, ω (a * b) = ω a * ω b) ∧
      (∀ a b, a ≠ b → v (ω a - ω b) = 1) := by sorry
