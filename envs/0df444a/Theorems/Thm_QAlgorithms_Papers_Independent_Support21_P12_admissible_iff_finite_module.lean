-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_admissible_iff_finite_module
-- name    : QAlgorithms.Papers.Independent.Support21.P12.admissible_iff_finite_module
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:13:35.45645+00:00
-- url     : https://prove2.me/theorems/567f55f0-a8c8-48f5-a4ee-3ee4284fd18b
-- title:
--   Admissible cyclotomic parameters and finite modules with contraction action
-- statement:
--   Let $F$ be algebraically closed and let $\widehat A_{n,F}$, $n\ge2$, be either actual affine BMW algebra, with arbitrary degenerate parameters or compatible ordinary unit parameters. Then
--
--   $$\begin{aligned}
--   &\text{there exist }r>0\text{ and an admissible root tuple }(u_1,\ldots,u_r)\\
--   &\qquad\Longleftrightarrow\quad
--   \widehat A_{n,F}\text{ has a finite dimensional module on which }e_1\text{ acts nontrivially}.
--   \end{aligned}$$
--
--   Admissibility means cyclic-family independence in the actual two-strand cyclotomic quotient. Ordinary roots must be units; degenerate roots may be zero. The module need not be simple, and no nonzero-contraction assumption is added to the equivalence.
--
--   **Formalization Note** A finite module is described in a chosen finite basis by a unital algebra homomorphism into a matrix algebra.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 17, Proposition 6.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Proposition 6.7, PDF p.17. No nonzero-e hypothesis is added to this
equivalence, and the finite dimensional module need not be simple. -/
theorem admissible_iff_finite_module (F : Type*) [Field F] [IsAlgClosed F]
    (omega : ℕ → F) (K : Kind F omega) (n : ℕ) (hn : 2 ≤ n) :
    HasAdmissibleRoots F omega K ↔ HasFiniteModule (F := F) (ae F omega K n 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
