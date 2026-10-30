-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_laplacianBase
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.laplacianBase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:22:44.300602+00:00
-- url     : https://prove2.me/theorems/8c91ed26-7c3b-4be1-88e7-51c9e747f5cc
-- title:
--   §3.5: exact Hermitian two-dimensional Laplacian encoding (76)–(87)
-- statement:
--   Let $N_x=2^{n_x}$, $N_y=2^{n_y}$, $N=N_xN_y$, and let real spacings $h_x,h_y$ be nonzero. With row-major index $a+bN_x$, define the nonperiodic finite-difference matrix with diagonal $-2(h_x^{-2}+h_y^{-2})$, horizontal neighbor entries $h_x^{-2}$, vertical neighbor entries $h_y^{-2}$, and all off-grid entries zero. Fixed labels (80)-(84), H5 on 000,010,011,100,101, and circuit (86) give
--   $$ U^\dagger=U,\qquad (\langle0|\otimes I)U(|0\rangle\otimes I)=A/[10(h_x^{-2}+h_y^{-2})]. $$
--   There are five flags. Arithmetic gate count is at most $C(n_x+2n_y)$ for $n_x+n_y\ge1$, with an absolute constant chosen before dimensions and spacings. Exact encoding also includes one-point coordinate directions and the one-point grid. This is a discrete operator statement, not an analytic finite-difference identity for arbitrary functions.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 21, §3.5: exact Hermitian two-dimensional Laplacian encoding (76)–(87)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.18-21, (76)-(87): exact Hermitian nonperiodic two-dimensional
Laplacian encoding. A single absolute arithmetic gate constant is uniform over
both grid dimensions and the nonzero spacings. Empty coordinate registers are
allowed; the asymptotic threshold avoids interpreting log 1 as zero total cost. -/
theorem laplacianBase :
    ∃ C : ℝ, 0 < C ∧ ∀ nx ny : ℕ,
      ∃ B : Scheme (nx + ny) 3 2 (nx + ny + 1), ∃ T : TransposeOracle B,
        LaplacianLabels nx ny B ∧
        (∀ l, (T.transpose l).2.val =
          if l.1.val = 1 ∨ l.1.val = 2 then
            (l.2.val + 2 ^ (nx + ny)) % 2 ^ (nx + ny + 1) else l.2.val) ∧
        (1 ≤ nx + ny → ∃ work, B.ArithmeticSize (C * (nx + 2 * ny)) work) ∧
        Fintype.card ((Bool × Bool) × Fin 8) = 2 ^ 5 ∧
        ∀ dx dy : ℝ, dx ≠ 0 → dy ≠ 0 →
          B.matrix (laplacianTable dx dy) = laplacian nx ny dx dy ∧
          QAlgorithms.IsBlockEncoding ((false, false), 0)
            (B.baseCircuit (laplacianTable dx dy) true)
            (10 * (1 / dx ^ 2 + 1 / dy ^ 2)) 0 (laplacian nx ny dx dy) ∧
          (B.baseCircuit (laplacianTable dx dy) true)ᴴ =
            B.baseCircuit (laplacianTable dx dy) true := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
