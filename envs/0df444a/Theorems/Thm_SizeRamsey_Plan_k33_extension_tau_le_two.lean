-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_extension_tau_le_two
-- name    : SizeRamsey.Plan.k33_extension_tau_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:32.163274+00:00
-- url     : https://prove2.me/theorems/cd9dac60-163b-541e-82d7-a54ac21e1a2b
-- title:
--   Plan: k33 extension tau le two
-- statement:
--   The Plan construction uses the k33 extension tau le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Extension.lean#L115-L180
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Extension.lean#L115-L180

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_Extension
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.k33_extension_tau_le_two
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (z : V)
    (hiso : Nonempty (erase G {z} ≃g k33MinusEdge))
    (hdeg : G.degree z = 4) :
    tau4 G ≤ 2 := by sorry
