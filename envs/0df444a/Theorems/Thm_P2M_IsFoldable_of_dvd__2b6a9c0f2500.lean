-- Prove2me | Theorems.Thm_P2M_IsFoldable_of_dvd__2b6a9c0f2500
-- name    : P2M_IsFoldable_of_dvd__2b6a9c0f2500
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:57:32.279025+00:00
-- url     : https://prove2.me/theorems/e98c625b-f4df-484a-9214-6b37668d8459
-- title:
--   P2 M Is Foldable of dvd  2b6a9c0f2500: P2 M Is Foldable of dvd  2b6a9c0f2500
-- statement:
--   Foldability is inherited by divisors
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L475-L477
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L475-L477

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem P2M_IsFoldable_of_dvd__2b6a9c0f2500 {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m n : ℕ}
    (h : IsFoldable D m) (hd : n ∣ m) : IsFoldable D n := by sorry

alias «IsFoldable».«of_dvd'» := P2M_IsFoldable_of_dvd__2b6a9c0f2500
