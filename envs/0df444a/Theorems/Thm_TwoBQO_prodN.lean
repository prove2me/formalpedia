-- Prove2me | Theorems.Thm_TwoBQO_prodN
-- name    : TwoBQO.prodN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:48.557226+00:00
-- url     : https://prove2.me/theorems/badf8ce1-97c6-4cb9-a63d-6c4f61dd0c73
-- title:
--   Two BQO: prod N
-- statement:
--   The Two BQO construction uses the prod N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L268-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L268-L269

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

theorem TwoBQO.prodN : ∀ n : ℕ, TwoBQO fun f g : Fin n → ℕ => ∀ i, f i ≤ g i := by sorry
