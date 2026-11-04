-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_of_proper
-- name    : ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_of_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:40.545891+00:00
-- url     : https://prove2.me/theorems/6340aba0-8c1f-4d80-896c-3b656f1ca047
-- title:
--   Ternary Cover Rank Fibers: affine Fiber card le of proper
-- statement:
--   The annihilator is selected using only the fixed conditional subspace.
--   The provided projection-fiber cap is applied once, with that same functional
--   on every coordinate.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L61-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L61-L78

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

theorem ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_of_proper (left right : E → ι → K) (P : ℕ)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (hV : V ≠ ⊤) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P := by sorry
