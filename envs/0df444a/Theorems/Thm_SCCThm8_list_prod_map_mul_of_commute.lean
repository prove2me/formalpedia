-- Prove2me | Theorems.Thm_SCCThm8_list_prod_map_mul_of_commute
-- name    : SCCThm8.list_prod_map_mul_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:26.791295+00:00
-- url     : https://prove2.me/theorems/62304b7d-aeae-4a8e-bbd8-0f9662e5e19f
-- title:
--   SCCThm8: list prod map mul of commute
-- statement:
--   Splitting a product of pointwise products, for commuting families.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L89-L101
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L89-L101

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.list_prod_map_mul_of_commute {G ι : Type*} [Group G] (l : List ι) (a b : ι → G)
    (h : ∀ i j, Commute (a i) (b j)) :
    (l.map fun i => a i * b i).prod = (l.map a).prod * (l.map b).prod := by sorry
