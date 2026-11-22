-- Prove2me | Theorems.Thm_Preorder_IsRegularSeq_exists_strictMono_dominating
-- name    : Preorder.IsRegularSeq.exists_strictMono_dominating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.056184+00:00
-- url     : https://prove2.me/theorems/6ed12c30-4d19-4825-aaf8-9eada0fc75bd
-- title:
--   Is Regular Seq: exists strict Mono dominating
-- statement:
--   **Strengthening of regularity.** If `f` is a regular sequence for a relation, then for every
--   threshold `n` there is a strictly monotone reindexing `e : ℕ → ℕ` whose values all lie at or
--   above `n` and which dominates `f` pointwise: `n ≤ e i` and `f i ≤ f (e i)` for every `i`. Proved
--   greedily via `exists_strictMono_of_greedy`, picking at each step a later index that is both `>`
--   the previous one and `≥ n`, available by regularity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L453-L460
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L453-L460

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

theorem Preorder.IsRegularSeq.exists_strictMono_dominating {Q : Type*} {le : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq le f) (n : ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, n ≤ e i ∧ le (f i) (f (e i)) := by sorry
