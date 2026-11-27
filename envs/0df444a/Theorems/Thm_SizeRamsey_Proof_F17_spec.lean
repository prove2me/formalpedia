-- Prove2me | Theorems.Thm_SizeRamsey_Proof_F17_spec
-- name    : SizeRamsey.Proof.F17_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:27.509807+00:00
-- url     : https://prove2.me/theorems/0ac1ac7b-316d-4601-aa32-5eec204dfe74
-- title:
--   Proof: F17 spec
-- statement:
--   The Proof construction uses the F17 spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L211-L214
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L211-L214

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof

theorem SizeRamsey.Proof.F17_spec :
    F17.Connected ∧ edgeCount F17 = 17 ∧
      ArrowsMatching4C4 F17 := by sorry
