-- Prove2me | Theorems.Thm_P2M_systemOfUnits_existence__26f57ceed3f9
-- name    : P2M_systemOfUnits_existence__26f57ceed3f9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:08.056801+00:00
-- url     : https://prove2.me/theorems/7636ea9b-a0dc-40bb-8bae-781e395297e2
-- title:
--   P2 M system Of Units existence  26f57ceed3f9: P2 M system Of Units existence  26f57ceed3f9
-- statement:
--   The P2 M system Of Units existence  26f57ceed3f9 construction uses the P2 M system Of Units existence  26f57ceed3f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L67-L80

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
open systemOfUnits
include hp hf
variable [Module.Free ℤ G]

theorem P2M_systemOfUnits_existence__26f57ceed3f9 [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    Nonempty (systemOfUnits p G (R + 1)) := by sorry

alias «systemOfUnits».«existence'» := P2M_systemOfUnits_existence__26f57ceed3f9
