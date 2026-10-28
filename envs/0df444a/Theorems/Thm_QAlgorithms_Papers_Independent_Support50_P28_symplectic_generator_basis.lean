-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_symplectic_generator_basis
-- name    : QAlgorithms.Papers.Independent.Support50.P28.symplectic_generator_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:20:33.175505+00:00
-- url     : https://prove2.me/theorems/68916549-2ce8-41bd-af84-9699c99d94b0
-- title:
--   Appendix A, (A1)–(A6): real symplectic Lie-algebra generators
-- statement:
--   Let $n\ge1$, use the real interleaved coordinates $(x_1,p_1,\ldots,x_n,p_n)$, and let $\sigma=\bigoplus_{j=1}^n\sigma_2$, where $\sigma_2=\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$. Put $\beta=\operatorname{diag}(1,-1)$ and $\delta=\left[\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right]$. Embed $\sigma_2,\beta,\delta$ on each individual mode, and on every unordered pair of distinct modes embed the four block matrices
--
--   $$\begin{bmatrix}0&\sigma_2\\\sigma_2&0\end{bmatrix},\quad
--   \begin{bmatrix}0&-I_2\\I_2&0\end{bmatrix},\quad
--   \begin{bmatrix}0&\delta\\\delta&0\end{bmatrix},\quad
--   \begin{bmatrix}0&\beta\\\beta&0\end{bmatrix}.$$
--
--   This family is linearly independent over $\mathbb R$ and spans precisely $\{K:K^T\sigma+\sigma K=0\}$. Its skew-symmetric members are linearly independent and span the intersection with $K^T=-K$. The total and compact-generator counts are, respectively,
--
--   $$3n+4\binom n2=2n^2+n,\qquad n+2\binom n2=n^2.$$
--
--   These are bases of infinitesimal real symplectic and compact passive algebras. The statement does not describe symmetric symplectic matrices as a subgroup.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 8, Appendix A, (A1)–(A6): real symplectic Lie-algebra generators

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)

open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.8, Appendix A (A1)--(A6): the specified embedded matrices form a
basis of the real symplectic Lie algebra; precisely n^2 of them are skew and
span the compact passive algebra. Symmetric symplectic matrices are not claimed
to form a subgroup. The source assumes n>=1. -/
theorem symplectic_generator_basis (n : ℕ) (hn : 0 < n) :
    LinearIndependent ℝ (sourceSymplecticGenerator (n := n)) ∧
    (↑(Submodule.span ℝ (Set.range (sourceSymplecticGenerator (n := n)))) : Set (OscillatorCovariance (Fin n))) =
      {K | InSymplecticAlgebra K} ∧
    Fintype.card (GeneratorIndex n) = 2 * n ^ 2 + n ∧
    LinearIndependent ℝ (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val) ∧
    (↑(Submodule.span ℝ (Set.range (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val))) :
      Set (OscillatorCovariance (Fin n))) = {K | InSymplecticAlgebra K ∧ K.transpose = -K} ∧
    Fintype.card (CompactGeneratorIndex n) = n ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
