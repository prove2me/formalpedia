-- Prove2me | Theorems.Thm_TwoBQO_lexSigmaQO_reflect
-- name    : TwoBQO.lexSigmaQO_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:30.095584+00:00
-- url     : https://prove2.me/theorems/69d5e388-1a70-447e-b823-0649ddc6b069
-- title:
--   Two BQO: lex Sigma QO reflect
-- statement:
--   **Sum theorem for 2-BQO along a quasi-order, restricted to a bad pair-sequence.** If `f` is
--   bad for `LexSumRelQO r s t`, then some restriction of `f` either has a bad index projection
--   (for `r`), or has a constant index `i` along which the second components form a bad
--   pair-sequence for `t i`. The constructive content underlying `TwoBQO.lexSigmaQO`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L323-L361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L323-L361

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
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)

theorem TwoBQO.lexSigmaQO_reflect {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (f : PairSeq (Σ i, s i))
    (hf_bad : PairSeq.IsBad (TwoBQO.LexSumRelQO r s t) f) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      PairSeq.IsBad r (fun m n hmn => (f (e m) (e n) (he_mono hmn)).1) ∨
      ∃ (i : ι) (hmem : ∀ m n (hmn : m < n), (f (e m) (e n) (he_mono hmn)).1 = i),
        PairSeq.IsBad (t i) fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he_mono hmn)).2 := by sorry
