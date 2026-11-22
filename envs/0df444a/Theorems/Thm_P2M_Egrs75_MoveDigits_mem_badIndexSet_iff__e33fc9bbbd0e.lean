-- Prove2me | Theorems.Thm_P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e
-- name    : P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:01.785585+00:00
-- url     : https://prove2.me/theorems/172ced1c-5fa4-4dbf-a6b7-4f0af4c2dfb8
-- title:
--   P2 M Egrs75 Move Digits mem bad Index Set iff  e33fc9bbbd0e: P2 M Egrs75 Move Digits mem bad Index Set iff  e33fc9bbbd0e
-- statement:
--   Membership in `badIndexSet` is exactly `BadAt` (local copy; the original
--   lives in `EgrsFinish_core`, which this file must not import).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L138-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean#L138-L152

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

theorem P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by sorry

alias «Egrs75».«MoveDigits».«mem_badIndexSet_iff'» := P2M_Egrs75_MoveDigits_mem_badIndexSet_iff__e33fc9bbbd0e
