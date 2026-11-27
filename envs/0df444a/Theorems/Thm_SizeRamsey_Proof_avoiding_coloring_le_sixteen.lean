-- Prove2me | Theorems.Thm_SizeRamsey_Proof_avoiding_coloring_le_sixteen
-- name    : SizeRamsey.Proof.avoiding_coloring_le_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:13.01872+00:00
-- url     : https://prove2.me/theorems/5d659cce-827a-5b2f-95e1-45f85a05d77d
-- title:
--   Proof: avoiding coloring le sixteen
-- statement:
--   Corollary C, colouring half, from the transversal half.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Coloring.lean#L49-L55
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Coloring.lean#L49-L55

module
public import Definitions.Def_SizeRamsey_Equality
public import Definitions.Def_SizeRamsey_ColoringBase
public import Definitions.Def_SizeRamsey_Coloring
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof

theorem SizeRamsey.Proof.avoiding_coloring_le_sixteen
    {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hconn : F.Connected) (hle : edgeCount F ≤ 16) :
    ∃ R : SimpleGraph V,
      R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by sorry
