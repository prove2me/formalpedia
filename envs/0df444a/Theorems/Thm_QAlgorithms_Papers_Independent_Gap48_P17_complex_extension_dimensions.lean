-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_complex_extension_dimensions
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.complex_extension_dimensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:09:12.511363+00:00
-- url     : https://prove2.me/theorems/298a99c8-4de6-44d0-901d-1e6497a9e6b1
-- title:
--   Theorem 6.5
-- statement:
--   Let $d>0$ and let $S$ be a full irreducible complex Clifford module for $\mathbb C^d$ with its complex bilinear metric. Define equivariant bracket subspaces $J_c^\sigma$ by exchange symmetry and, in even dimension, $J_c^{\sigma\iota}$ by the same-half or mixed-half support relative to a compatible semispinor split. Let $L_c^\sigma$ and $L_c^{\sigma\iota}$ be their complex dimensions. The complete table is
--   $$\begin{array}{c|cccccccc}d\bmod8&5&6&7&0&1&2&3&4\\\hline(L_c^+,L_c^-)\text{ or }(L_c^{++},L_c^{+-},L_c^{-+},L_c^{--})&(0,1)&(0,0,2,0)&(0,1)&(0,1,0,1)&(1,0)&(2,0,0,0)&(1,0)&(0,1,0,1)\end{array}$$
--   The spinor splits exactly when $d$ is even. The periodic extensions satisfy
--   $$L_c^+(-d)=L_c^-(d),\qquad L_c^{+\iota}(-d)=L_c^{-\iota}(d).$$
--   All dimensions, coefficients, duals and invariance equations are complex-linear; residue zero is represented by positive dimensions such as eight.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 39, Theorem 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Theorem 6.5, PDF p. 39: dimensions over C, full table, periodicity and both mirrors.
Residue zero denotes a positive-dimensional representative, never the zero space. -/
theorem complex_extension_dimensions :
    (∀ (d : ℕ), 0 < d →
      ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
        (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S),
        actualTotalDimensions rho = complexTotalTable d ∧
        (Nonempty (SpinSplitting rho) ↔ Even d) ∧
        ∀ h : SpinSplitting rho, actualRefinedDimensions rho h = complexRefinedTable d) ∧
    (∀ d : ℤ,
      complexTotalTable (d + 8) = complexTotalTable d ∧
      complexTotalTable (-d) = ((complexTotalTable d).2, (complexTotalTable d).1) ∧
      (Even d → complexRefinedTable (d + 8) = complexRefinedTable d ∧
        complexRefinedTable (-d) = ((complexRefinedTable d).2.2.1,
          (complexRefinedTable d).2.2.2, (complexRefinedTable d).1, (complexRefinedTable d).2.1))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
