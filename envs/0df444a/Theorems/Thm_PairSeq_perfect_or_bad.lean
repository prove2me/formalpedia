-- Prove2me | Theorems.Thm_PairSeq_perfect_or_bad
-- name    : PairSeq.perfect_or_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:24.225941+00:00
-- url     : https://prove2.me/theorems/c074ba97-c87e-4d82-b887-b0287aa01435
-- title:
--   Pair Seq: perfect or bad
-- statement:
--   Every pair-sequence has a restriction that is perfect or bad for `r`: colour each triple
--   `h < i < j` by whether `r (f h i) (f i j)` holds and apply `infinite_ramsey_triples`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L85-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L85-L102

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
open PairSeq

theorem PairSeq.perfect_or_bad {α : Type*} (r : α → α → Prop) (f : PairSeq α) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      IsPerfect r (restrict f e he_mono) ∨ IsBad r (restrict f e he_mono) := by sorry
