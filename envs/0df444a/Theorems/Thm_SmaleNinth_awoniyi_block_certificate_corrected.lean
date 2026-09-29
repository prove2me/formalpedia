-- Prove2me | Theorems.Thm_SmaleNinth_awoniyi_block_certificate_corrected
-- name    : SmaleNinth.awoniyi_block_certificate_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T09:25:41.108588+00:00
-- url     : https://prove2.me/theorems/b0b7b3be-ab70-48c5-9f2c-81292ff079b3
-- title:
--   Decode an Awoniyi block certificate into a positive LP certificate
-- statement:
--   This corrected decoder follows the sign convention of Awoniyi's primal-dual equation system. A nonnegative primal block is split as `xp - xm`, and the nonnegative slack vector satisfies `A.mulVec (xp - xm) - s = b`, equivalently `A.mulVec (xp - xm) = b + s`. A nonnegative dual block is orthogonal to the columns of `A` and supported on the slack. The resulting primal vector is feasible and the dual block is a valid positive complementarity certificate. The original node with the opposite slack sign is retained as a retired target; this node is its source-faithful replacement.
-- source:
--   Samuel Awoniyi, *A strongly polynomial-time algorithm for the general linear programming problem*, arXiv:2503.12041v10, Sections 2, 4, 6, and 7, https://arxiv.org/abs/2503.12041

import Definitions.Def_Polyhedron
import Mathlib.Tactic

open Matrix LinearOptimization

theorem SmaleNinth.awoniyi_block_certificate_corrected {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xp xm : Fin n → ℝ) (s y : Fin m → ℝ)
    (hxp : ∀ j, 0 ≤ xp j)
    (hxm : ∀ j, 0 ≤ xm j)
    (hs : ∀ i, 0 ≤ s i)
    (hblock : A.mulVec xp - A.mulVec xm - s = b)
    (hy : ∀ i, 0 ≤ y i)
    (hyA : ∀ k, ∑ i, y i * A i k = 0)
    (hcomp : ∀ i, y i * s i = 0) :
    ∃ x : Fin n → ℝ,
      x ∈ polyhedron A b ∧
      (∀ i, 0 ≤ y i) ∧
      (∀ k, ∑ i, y i * A i k = 0) ∧
      (∀ i, y i * ((A.mulVec x) i - b i) = 0) := by sorry
