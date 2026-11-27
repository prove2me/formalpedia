-- Prove2me | Theorems.Thm_SizeRamsey_Proof_equality_classification
-- name    : SizeRamsey.Proof.equality_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:11.24288+00:00
-- url     : https://prove2.me/theorems/eaaf0468-f3ba-5bf4-9023-729a4d63fd65
-- title:
--   Proof: equality classification
-- statement:
--   The Proof construction uses the equality classification property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality.lean#L57-L80
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality.lean#L57-L80

module
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
public import Definitions.Def_SizeRamsey_Equality_Mixed
public import Definitions.Def_SizeRamsey_Equality_Cubic
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
public import Definitions.Def_SizeRamsey_Equality
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Proof

theorem SizeRamsey.Proof.equality_classification
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected)
    (hpos : 0 < edgeCount G)
    (hle : edgeCount G ≤ 16) :
    4 * tau4 G = edgeCount G ↔
      Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨
      Nonempty (G ≃g wheel5) ∨
      Nonempty (G ≃g k33MinusEdge) ∨
      Nonempty (G ≃g octahedron) := by sorry
