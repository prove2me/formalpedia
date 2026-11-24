-- Prove2me | Theorems.Thm_ValiantBorder_affineDetCircuit
-- name    : ValiantBorder.affineDetCircuit
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:21:24.663472+00:00
-- url     : https://prove2.me/theorems/551882b5-e98d-4507-a3be-ff9b7919ba4a
-- title:
--   Polynomial-size division-free circuits for affine determinants
-- statement:
--   Over any commutative ring, the determinant of an $n$ by $n$ matrix of affine linear forms in $v$ variables has a division-free arithmetic circuit with at most $(v+n+2)^8$ gates. The count includes scalar inputs, variable inputs and binary arithmetic gates. The circuit uses [Bird’s determinant recurrence](https://doi.org/10.1016/j.ipl.2011.08.006). The exponent eight is a convenient uniform bound for the gate model in this mission.
-- source:
--   R. S. Bird, A simple division-free algorithm for computing determinants, Information Processing Letters 111 (2011), pp. 1072–1074, https://doi.org/10.1016/j.ipl.2011.08.006. The recurrence is verified in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean. The explicit gate budget is derived here.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.affineDetCircuit {R V : Type} [CommRing R] [Fintype V] {n : ℕ}
    (c : Fin n → Fin n → R) (a : Fin n → Fin n → V → R) :
    Statement.Computes (Matrix.of fun i j =>
      MvPolynomial.C (c i j) + ∑ v, MvPolynomial.C (a i j v) * MvPolynomial.X v).det
      ((Fintype.card V + n + 2)^8) := by sorry
