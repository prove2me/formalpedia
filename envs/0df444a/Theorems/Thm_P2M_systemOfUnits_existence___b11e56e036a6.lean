-- Prove2me | Theorems.Thm_P2M_systemOfUnits_existence___b11e56e036a6
-- name    : P2M_systemOfUnits_existence___b11e56e036a6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:12.624154+00:00
-- url     : https://prove2.me/theorems/a45f79ce-26c0-43c6-b1ab-eb463f514108
-- title:
--   P2 M system Of Units existence   b11e56e036a6: P2 M system Of Units existence   b11e56e036a6
-- statement:
--   The P2 M system Of Units existence   b11e56e036a6 construction uses the P2 M system Of Units existence   b11e56e036a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean#L82-L87

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

theorem P2M_systemOfUnits_existence___b11e56e036a6 [Module A G] {R : ℕ} (hR : R ≤ s) : Nonempty (systemOfUnits p G R) := by sorry

alias «systemOfUnits».«existence''» := P2M_systemOfUnits_existence___b11e56e036a6
