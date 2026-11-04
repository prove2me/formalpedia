-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_one
-- name    : ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:41.057454+00:00
-- url     : https://prove2.me/theorems/6a605432-6385-47f7-8de1-cbfdcde087c5
-- title:
--   Ternary Cover Rank Fibers: affine Fiber card le one
-- statement:
--   A rank-zero conditional subspace fixes both endpoint words.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L81-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L81-L95

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]

theorem ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_one (left right : E → ι → K)
    (hinj : Function.Injective (fun e => (left e, right e))) (offset : ι → K × K) :
    (affineFiber left right (⊥ : Submodule K (K × K)) offset).card ≤ 1 := by sorry
