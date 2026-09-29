-- Prove2me | Theorems.Thm_PassivityTorus_shift_back_forward
-- name    : PassivityTorus.shift_back_forward
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:20:38.884243+00:00
-- url     : https://prove2.me/theorems/64671722-03d2-42a6-abbb-953e42f9c277
-- title:
--   Stepping back then forward returns to the start
-- statement:
--   For every site $x$ of the periodic lattice $(\mathbb{Z}/L\mathbb{Z})^q$ (with $L \ge 1$) and every axis $a$,
--
--   $$
--   (x - e_a) + e_a = x .
--   $$
--
--   One step back along axis $a$ followed by one step forward returns to the original site. This is the fact that makes the one-step shift a bijection of the lattice, which is needed to reindex the power sum.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (extended to a q-dimensional periodic lattice): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorus
theorem shift_back_forward {q L : ℕ} [NeZero L] (x : Site q L) (a : Fin q) :
    shift (shift x a (-1)) a 1 = x := by sorry
end PassivityTorus
