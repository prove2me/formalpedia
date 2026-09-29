-- Prove2me | Theorems.Thm_PassivityRing_passive_of_symm
-- name    : PassivityRing.passive_of_symm
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:57:09.938595+00:00
-- url     : https://prove2.me/theorems/6a5c2581-bdf2-44dc-a878-8e322cb4893f
-- title:
--   Symmetric links are passive
-- statement:
--   Let $N \ge 1$ and $d$ be natural numbers and let $W_0, \dots, W_{N-1}$ be real $d\times d$ matrices with $W_i^{\mathsf T} = W_i$ for every $i$. Then for every choice of velocities $v_0, \dots, v_{N-1} \in \mathbb{R}^d$ (indices modulo $N$),
--
--   $$
--   \sum_{i} v_i \cdot \bigl( W_i\, v_{i+1} - W_{i-1}\, v_{i-1} \bigr) = 0 .
--   $$
--
--   This is the "if" direction of the goal, and it holds on rings of every size.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

namespace PassivityRing
theorem passive_of_symm (N d : ℕ) [NeZero N]
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ) (hW : ∀ i, (W i)ᵀ = W i)
    (v : Fin N → (Fin d → ℝ)) : power N d W v = 0 := by sorry
end PassivityRing
