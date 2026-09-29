-- Prove2me | Theorems.Thm_PassivityTorus_passive_of_symm
-- name    : PassivityTorus.passive_of_symm
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:21:52.42609+00:00
-- url     : https://prove2.me/theorems/bd1432ac-0f44-43fb-b10a-5b6b198cf3d4
-- title:
--   Symmetric links are passive
-- statement:
--   Let $W(x,a)$ be real $d\times d$ link matrices on the periodic lattice $(\mathbb{Z}/L\mathbb{Z})^q$ with $L \ge 1$, and suppose every one is symmetric, $W(x,a)^{\mathsf T} = W(x,a)$. Then for every velocity field $v$,
--
--   $$
--   P_W(v) = 0 .
--   $$
--
--   This is the "if" direction of the goal, valid for every lattice size.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (extended to a q-dimensional periodic lattice): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorus
theorem passive_of_symm (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ) (hW : ∀ x a, (W x a)ᵀ = W x a)
    (v : Site q L → (Fin d → ℝ)) : power q L d W v = 0 := by sorry
end PassivityTorus
