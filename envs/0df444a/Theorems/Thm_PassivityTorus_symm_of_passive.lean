-- Prove2me | Theorems.Thm_PassivityTorus_symm_of_passive
-- name    : PassivityTorus.symm_of_passive
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:22:17.302593+00:00
-- url     : https://prove2.me/theorems/67a76ba6-36ac-4052-ab99-e2dabad35746
-- title:
--   Passive forces symmetric (needs $L \ge 3$)
-- statement:
--   Let $L \ge 3$, and let $W(x,a)$ be real $d\times d$ link matrices on the periodic lattice $(\mathbb{Z}/L\mathbb{Z})^q$. If $P_W(v) = 0$ for every velocity field $v$, then every link matrix is symmetric:
--
--   $$
--   W(x,a)^{\mathsf T} = W(x,a) \qquad \text{for all sites } x \text{ and axes } a.
--   $$
--
--   This is the "only if" direction of the goal. The hypothesis $L \ge 3$ is necessary: at $L = 2$ the forward and backward neighbours coincide, and a non-symmetric matrix on every link gives zero power.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (extended to a q-dimensional periodic lattice): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a) and correction 4 (at least 3 sites): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorus
theorem symm_of_passive (q L d : ℕ) [NeZero L] (hL : 3 ≤ L)
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ v : Site q L → (Fin d → ℝ), power q L d W v = 0) :
    ∀ x a, (W x a)ᵀ = W x a := by sorry
end PassivityTorus
