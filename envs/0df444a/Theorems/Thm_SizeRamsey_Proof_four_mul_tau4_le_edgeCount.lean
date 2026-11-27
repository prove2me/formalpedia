-- Prove2me | Theorems.Thm_SizeRamsey_Proof_four_mul_tau4_le_edgeCount
-- name    : SizeRamsey.Proof.four_mul_tau4_le_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:05.831096+00:00
-- url     : https://prove2.me/theorems/b0788cb3-fd1e-5d2a-a592-d12ffa4c9550
-- title:
--   Proof: four mul tau4 le edge Count
-- statement:
--   The Proof construction uses the four mul tau4 le edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Universal.lean#L123-L126
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Universal.lean#L123-L126

module
public import Definitions.Def_SizeRamsey_Reductions
public import Definitions.Def_SizeRamsey_Universal
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Proof

theorem SizeRamsey.Proof.four_mul_tau4_le_edgeCount
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    4 * tau4 G ≤ edgeCount G := by sorry
