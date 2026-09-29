-- Prove2me | Theorems.Thm_PassivityTorus_passive_iff_symm
-- name    : PassivityTorus.passive_iff_symm
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:23:53.187137+00:00
-- url     : https://prove2.me/theorems/da9532ef-2879-40cf-90b4-5cb1699f31a1
-- title:
--   Zero net power $\iff$ every link coupling is symmetric, on a $q$-dimensional lattice ($L \ge 3$)
-- statement:
--   Let $q$ and $d$ be natural numbers and $L \ge 3$. On the periodic cubic lattice $(\mathbb{Z}/L\mathbb{Z})^q$, let each link $(x,a)$ carry a real $d\times d$ matrix $W(x,a)$, with total power
--
--   $$
--   P_W(v) = \sum_{x} \sum_{a=0}^{q-1} v(x) \cdot \Bigl( W(x,a)\, v(x+e_a) - W(x-e_a,a)\, v(x-e_a) \Bigr).
--   $$
--
--   Then
--
--   $$
--   \bigl( P_W(v) = 0 \ \text{for every } v \bigr) \iff \bigl( W(x,a)^{\mathsf T} = W(x,a) \ \text{for every } x, a \bigr).
--   $$
--
--   A per-link neighbour coupling on a lattice of any dimension does no net work for every motion exactly when every link matrix is symmetric. It does not assert that the coupling commutes with any complex structure.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (extended to a q-dimensional periodic lattice): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorus
theorem passive_iff_symm (q L d : ℕ) [NeZero L] (hL : 3 ≤ L)
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ) :
    (∀ v : Site q L → (Fin d → ℝ), power q L d W v = 0)
      ↔ ∀ x a, (W x a)ᵀ = W x a := by sorry
end PassivityTorus
