-- Prove2me | Theorems.Thm_SizeRamsey_Proof_connected_transversal_le_three
-- name    : SizeRamsey.Proof.connected_transversal_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:21.444332+00:00
-- url     : https://prove2.me/theorems/4eca641b-3853-47b8-9716-4dc5a909d209
-- title:
--   Proof: connected transversal le three
-- statement:
--   Corollary C, transversal half: a `C₄`-transversal of at most three vertices.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Coloring.lean#L20-L46
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Coloring.lean#L20-L46

module
public import Definitions.Def_SizeRamsey_Equality
public import Definitions.Def_SizeRamsey_ColoringBase
public import Definitions.Def_SizeRamsey_Coloring
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof

theorem SizeRamsey.Proof.connected_transversal_le_three
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hle : edgeCount G ≤ 16) :
    ∃ S : Finset V,
      c4Transversal G S ∧ S.card ≤ 3 := by sorry
