-- Prove2me | Theorems.Thm_PassivityRing_passive_iff_symm
-- name    : PassivityRing.passive_iff_symm
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T22:01:01.508864+00:00
-- url     : https://prove2.me/theorems/b590f7d4-f877-48f6-898f-512623cac3e3
-- title:
--   Zero net power $\iff$ every link coupling is symmetric (rings of $N \ge 3$ sites)
-- statement:
--   Let $N \ge 3$ and $d$ be natural numbers. On a ring of $N$ sites (indices modulo $N$), each site carries a velocity $v_i \in \mathbb{R}^d$ and each link carries a real $d\times d$ matrix $W_i$. The total power of the coupling is
--
--   $$
--   P_W(v) = \sum_{i} v_i \cdot \bigl( W_i\, v_{i+1} - W_{i-1}\, v_{i-1} \bigr).
--   $$
--
--   Then
--
--   $$
--   \bigl( P_W(v) = 0 \ \text{for every } v \bigr) \iff \bigl( W_i^{\mathsf T} = W_i \ \text{for every } i \bigr).
--   $$
--
--   So a per-link neighbour coupling on a ring of at least three sites does no net work for every motion exactly when every link matrix is symmetric. The ring-size condition is necessary, and the statement does not assert that the coupling commutes with any complex structure.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

namespace PassivityRing
theorem passive_iff_symm (N d : ℕ) [NeZero N] (hN : 3 ≤ N)
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ) :
    (∀ v : Fin N → (Fin d → ℝ), power N d W v = 0) ↔ ∀ i, (W i)ᵀ = W i := by sorry
end PassivityRing
