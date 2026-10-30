-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_fourier_reconstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.fourier_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:57:41.285801+00:00
-- url     : https://prove2.me/theorems/00956059-326f-4410-815d-73eebe164f8d
-- title:
--   Fact 2: Fourier reconstruction on a physical Schur block
-- statement:
--   Let $d\ge1$, $n\ge0$, and let $\alpha\vdash n$ have at most $d$ rows. Let $\phi^\alpha$ be its unitary irreducible representation of $S_n$, of actual dimension $d_\alpha$, and let $V_\tau$ permute the $n$ physical tensor factors. For every complex $d_\alpha\times d_\alpha$ matrix $X$,
--
--   $$
--   \sum_{\tau\in S_n}\operatorname{Tr}\!\left(X\phi^\alpha(\tau^{-1})\right)V_\tau
--   =\frac{n!}{d_\alpha}\left(I_{U_\alpha}\otimes X\right).
--   $$
--
--   The operator on the right is extended by zero on other physical isotypic blocks. It reconstructs an arbitrary operator in a specified Schur block; $X$ need not be a state.
--
--   **Formalization Note** The physical block is transported through the frozen Schur transform independently of the Fourier sum.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 10, Fact 2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Fact 2: Fourier reconstruction on a physical Schur block for every complex
X, including non-Hermitian operators (PDF p.10, (42)). -/
theorem fourier_reconstruction (d n : ℕ) (hd : 0 < d)
    (alpha : QAlgorithms.Schur.Partition d n)
    (X : Matrix (Fin (irrepDim alpha)) (Fin (irrepDim alpha)) ℂ) :
    (∑ tau : Equiv.Perm (Fin n),
      (X * spechtActionMatrix alpha tau⁻¹).trace • QAlgorithms.Schur.tensorPermutation d n tau) =
    ((n.factorial : ℂ) / (irrepDim alpha : ℂ)) • physicalBlock alpha X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
