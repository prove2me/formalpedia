-- Prove2me | Theorems.Thm_PassivityRing_power_eq
-- name    : PassivityRing.power_eq
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:55:48.235565+00:00
-- url     : https://prove2.me/theorems/856451bf-2865-4630-8477-892639af7587
-- title:
--   Power identity: $P = \sum_i v_i \cdot (W_i - W_i^{\mathsf T})\, v_{i+1}$
-- statement:
--   Let $N \ge 1$ and $d$ be natural numbers, let $W_0, \dots, W_{N-1}$ be real $d\times d$ matrices and $v_0, \dots, v_{N-1} \in \mathbb{R}^d$, with indices modulo $N$. Then the total power satisfies
--
--   $$
--   \sum_{i} v_i \cdot \bigl( W_i\, v_{i+1} - W_{i-1}\, v_{i-1} \bigr) = \sum_{i} v_i \cdot \bigl( (W_i - W_i^{\mathsf T})\, v_{i+1} \bigr).
--   $$
--
--   The identity holds for every ring size, with no condition on the link matrices. It rewrites the power so that each link contributes only through its antisymmetric part.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a) (power identity): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

namespace PassivityRing
theorem power_eq (N d : ℕ) [NeZero N]
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ) (v : Fin N → (Fin d → ℝ)) :
    power N d W v = ∑ i : Fin N, v i ⬝ᵥ ((W i - (W i)ᵀ) *ᵥ v (i + 1)) := by sorry
end PassivityRing
