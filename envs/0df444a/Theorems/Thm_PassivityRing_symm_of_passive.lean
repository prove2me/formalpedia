-- Prove2me | Theorems.Thm_PassivityRing_symm_of_passive
-- name    : PassivityRing.symm_of_passive
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:59:36.257389+00:00
-- url     : https://prove2.me/theorems/b54dd823-01ea-4d7b-b590-a04d178fdf86
-- title:
--   Passive forces symmetric (rings of $N \ge 3$ sites)
-- statement:
--   Let $N \ge 3$ and $d$ be natural numbers and let $W_0, \dots, W_{N-1}$ be real $d\times d$ matrices. Suppose that for every choice of velocities $v_0, \dots, v_{N-1} \in \mathbb{R}^d$ (indices modulo $N$),
--
--   $$
--   \sum_{i} v_i \cdot \bigl( W_i\, v_{i+1} - W_{i-1}\, v_{i-1} \bigr) = 0 .
--   $$
--
--   Then every link matrix is symmetric: $W_i^{\mathsf T} = W_i$ for all $i$.
--
--   This is the "only if" direction of the goal. The hypothesis $N \ge 3$ is necessary: on rings of $1$ or $2$ sites there are non-symmetric link matrices with zero power for every motion.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a) and correction 4 (ring of ≥ 3 sites): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

namespace PassivityRing
theorem symm_of_passive (N d : ℕ) [NeZero N] (hN : 3 ≤ N)
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ v : Fin N → (Fin d → ℝ), power N d W v = 0) :
    ∀ i, (W i)ᵀ = W i := by sorry
end PassivityRing
