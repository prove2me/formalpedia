-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_pow_finrank
-- name    : ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_pow_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:41.398429+00:00
-- url     : https://prove2.me/theorems/fac0707d-977e-4cd4-89f1-65887650761e
-- title:
--   Ternary Cover Rank Fibers: affine Fiber card le pow finrank
-- statement:
--   Conditional rank increments zero, one, and two cost respectively one,
--   `P`, and `P²` completions.  This includes the full two-dimensional fiber.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L99-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean#L99-L122

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

theorem ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_pow_finrank (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P ^ Module.finrank K V := by sorry
