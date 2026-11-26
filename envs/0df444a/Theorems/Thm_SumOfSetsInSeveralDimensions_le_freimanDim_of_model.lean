-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_le_freimanDim_of_model
-- name    : SumOfSetsInSeveralDimensions.le_freimanDim_of_model
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:37.410803+00:00
-- url     : https://prove2.me/theorems/6f7edc65-8262-5662-a41a-4a9bcbd74fbd
-- title:
--   Sum Of Sets In Several Dimensions: le freiman Dim of model
-- statement:
--   A Freiman model of `X` of dimension `d ≤ |X|` shows that `d ≤ freimanDim X`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimension.lean#L52-L55
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimension.lean#L52-L55

module
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset

theorem SumOfSetsInSeveralDimensions.le_freimanDim_of_model {G : Type*} [DecidableEq G] [AddCommMonoid G] {X : Finset G} {d : ℕ}
    (hd : d ≤ #X) (hmodel : freimanModelDim X d) : d ≤ freimanDim X := by sorry
