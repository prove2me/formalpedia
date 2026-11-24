-- Prove2me | Theorems.Thm_ValiantBorder_lawTapePieces
-- name    : ValiantBorder.lawTapePieces
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:12:51.672895+00:00
-- url     : https://prove2.me/theorems/96255a3d-aa19-42d2-963a-e99335163de7
-- title:
--   Exchange laws give bounded pieces of a tape computation
-- statement:
--   Exchange laws with sufficient quantitative gain allow computations of any finite tape automaton to be split into pieces. The decomposition controls the number of pieces, their boundary sizes, and the time required to describe them.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Pieces.lean#L653).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Pieces.lean#L653.

import Definitions.Def_ValiantBorder_tapePieces

open Finset Nc Nc.Tow Nc.Vp Paper
open Nc.Tower (ee)

theorem ValiantBorder.lawTapePieces {A : Type} [CommRing A] {h : ℕ} [NeZero h] (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a e : ℕ, 300 ≤ e ∧ ∀ (Γ S Q : Type) [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
      (mu : Nc.Letter S Unit Γ → Matrix Q Q A),
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧
        ∀ T k, v ^ a ≤ T → 2 ≤ k → k ≤ v ^ 64 →
          Nonempty (PieceCut (kindList A ((univ : Finset VL.Di).toList.map VL.L)) mu (2 ^ ee h)
            (goodBound VL.C₁ VL.a₁) v K T k C) := by sorry
