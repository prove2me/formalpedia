-- Prove2me | Theorems.Thm_TwoBQO_embedForAll_wqo
-- name    : TwoBQO.embedForAll_wqo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:58.227695+00:00
-- url     : https://prove2.me/theorems/70a0dfed-81d8-487e-ad1e-62ec9a692f4d
-- title:
--   Two BQO: embed For All wqo
-- statement:
--   **`EmbedForAll r` is WQO on `ℕ → Q` whenever `r` is 2-BQO on `Q`.**
--
--   **Proof sketch.** Split each sequence `F n` into a regular tail `G n` preceded by a finite head
--   `w n` (`WellQuasiOrdered.eventuallyRegular`). Apply the product of Higman's lemma on the heads
--   (`WellQuasiOrdered.sublistForall₂`) and of the domination order on the downsets
--   `S n = {x | ∃ i, r x (G n i)}` of the tails (`TwoBQO.dom_twoBQO`) to a pair `a < b` with both
--   components related. The domination relation on downsets, combined with regularity, produces a
--   pointwise embedding of the tail `G a` into `G b`; the Higman relation on the heads produces a
--   pointwise embedding of the head `w a` into `w b`; `embed_combine` splices the two into a single
--   embedding of `F a` into `F b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L509-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L509-L560

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

theorem TwoBQO.embedForAll_wqo {α : Type*} {r : α → α → Prop} [IsPreorder α r] (hr : TwoBQO r) :
    WellQuasiOrdered (EmbedForAll r) := by sorry
