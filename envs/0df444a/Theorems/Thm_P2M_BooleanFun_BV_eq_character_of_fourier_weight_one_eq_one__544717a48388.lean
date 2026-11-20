-- Prove2me | Theorems.Thm_P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388
-- name    : P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:21.888036+00:00
-- url     : https://prove2.me/theorems/89554599-b36d-4dfc-88f2-88c12d7311d8
-- title:
--   P2 M Boolean Fun BV eq character of fourier weight one eq one  544717a48388: P2 M Boolean Fun BV eq character of fourier weight one eq one  544717a48388
-- statement:
--   A Boolean valued function with degree one Fourier weight equal to one
--   must be `±1` times a degree one character.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L226-L232
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L226-L232

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388 (hbv : BooleanValued f) (hn : n>0)
    (hf : fourierWeight 1 f = 1):
    ∃ S ∈ {S|S.card = 1}, ∃ c : ℝ, f = c•χ S := by sorry

alias «BooleanFun».«BV».«eq_character_of_fourier_weight_one_eq_one'» := P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388
